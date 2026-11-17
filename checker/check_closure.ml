(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The axioms and the relaxed typing flags that a constant rests on, for
    [rocqchk -compare].

    The closure follows what [Print Assumptions] walks (vernac/assumptions.ml,
    which the checker cannot link): the body and the type of a constant, the
    parameters, arities and constructor types of an inductive block, and, for
    a constant that a module signature leaves without a body, the body that the
    module's implementation gives it. The implementation is read from the
    environment, which keeps the implementation of every module it holds, so
    an object that only the implementation declares is found too, whether its
    library was checked, loaded with -norec, or admitted. *)

open Util
open Names
open Declarations
open Mod_declarations

(** {6 Implementations hidden by module signatures}

    The closure resolves a term in the declaration view that typed it. A
    public declaration uses its environment view; a bodyless public
    declaration falls back to its implementation and then follows that
    implementation's fields. This prevents an independent signature proof
    from replacing a proof witness that depends on a relaxed kernel check. *)

type view = Public | Implementation

type vref = view * GlobRef.t

type field_index = {
  constants : constant_body Id.Map.t;
  minds : mutual_inductive_body Id.Map.t;
  modules : module_body Id.Map.t;
}

let empty_field_index = {
  constants = Id.Map.empty;
  minds = Id.Map.empty;
  modules = Id.Map.empty;
}

let index_fields fields =
  let add_mind label mib index =
    let minds = Id.Map.add label mib index.minds in
    let minds = Array.fold_left (fun minds mip ->
        Id.Map.add mip.mind_typename mib minds) minds mib.mind_packets in
    { index with minds }
  in
  List.fold_left (fun index (label, field) -> match field with
      | SFBconst cb -> { index with constants = Id.Map.add label cb index.constants }
      | SFBmind mib -> add_mind label mib index
      | SFBmodule mb -> { index with modules = Id.Map.add label mb index.modules }
      | SFBmodtype _ | SFBrules _ -> index)
    empty_field_index fields

let find_module fields label = Id.Map.find_opt label fields.modules
let find_constant fields label = Id.Map.find_opt label fields.constants
let find_mind fields label = Id.Map.find_opt label fields.minds

type node = {
  refs : vref list;
  (* the objects the selected declaration mentions, with the view that
     typed each reference *)
  axiom : bool;
  (* no body: a constant without one, an opaque constant whose body cannot be
     read, or an object neither the environment nor an implementation
     resolves, which is reported rather than left out *)
  flags : (string * GlobRef.t) list;
  (* the relaxed typing conditions the selected object relies on,
     (kind, object); an inductive block's object is its first inductive *)
}

type closure_state = {
  env : Environ.env;
  access : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm;
  mutable fields : field_index ModPath.Map.t;
  (* the indexed fields of the implementation of each module looked up so far *)
  mutable public_nodes : node GlobRef.Map.t;
  mutable implementation_nodes : node GlobRef.Map.t;
  (* each object reached so far, keyed by its constant or by the first
     inductive of its block, in the declaration view that typed its use.
     [GlobRef.Map] and [GlobRef.Set] compare user names ([GlobRef.UserOrd]),
     which the walk needs: a transparent alias and its target share a
     canonical name, and each is resolved by its own user name
     ([lookup_constant]), so a key by canonical name could let the alias's
     node, which has a body, stand for its target, which may be an axiom. *)
  mutable gen : int;
  keys : Constr.t array;
  gens : int array;
  (* the cache of [seen] *)
}

let rec fields_of_functor f subs mp0 args = function
  | NoFunctor a -> f subs mp0 args a
  | MoreFunctor (mbid, _, e) ->
    match args with
    | [] -> raise Not_found (* an unapplied functor has no fields *)
    | mpa :: args ->
      let subs =
        Mod_subst.join (Mod_subst.map_mbid mbid mpa (Mod_subst.empty_delta_resolver mpa)) subs in
      fields_of_functor f subs mp0 args e

(* As in vernac/assumptions.ml: a module whose parent's implementation cannot
   be read is taken from the environment, which holds its signature. *)
let rec lookup_module_in_impl st mp = match mp with
  | MPfile _ | MPbound _ -> Environ.lookup_module mp st.env
  | MPdot (mp', lab) ->
    match fields_of_mp st mp' with
    | fields ->
      (match find_module fields lab with
       | Some mb -> mb
       | None -> Environ.lookup_module mp st.env)
    | exception Not_found -> Environ.lookup_module mp st.env

and fields_of_mp st mp =
  match ModPath.Map.find_opt mp st.fields with
  | Some fields -> fields
  | None ->
    let mb = lookup_module_in_impl st mp in
    let raw_fields, inner_mp, subs = fields_of_mb st Mod_subst.empty_subst mp mb [] in
    let fields =
      match mod_expr mb, ModPath.equal inner_mp mp with
      | (Algebraic _, false) ->
        (* [mb] is [Module mp := E] or [Module mp : T := E], and [inner_mp]
           is the module that [E] reduces to: the aliased module, also through
           a functor whose body is an alias, or the functor of an application
           whose body is a structure. The fields are [inner_mp]'s, renamed to
           [mp] and strengthened as the kernel types [Module mp := inner_mp]
           ([Modops.strengthen_and_subst_module_body]): each constant that is
           not a transparent definition there becomes a definition equal to
           the same constant of [inner_mp]. This is sound because the kernel
           makes each such field the object of [inner_mp] itself: the walk
           goes on to that object, in its own declaration and implementation,
           so a field reached through the alias rests on the axioms of the
           original and is never an axiom of its own. This reads no resolver
           of [mb], unlike vernac/assumptions.ml's [fields_of_mp] (and its
           "XXX" note) at this point. When [inner_mp] is a functor, the
           strengthened module is a functor too, which has no fields
           ([Not_found]): the constants of [mp] are then the environment's,
           where one without a body counts as an axiom. *)
        let mp_from = inner_mp in
        let source = lookup_module_in_impl st mp_from in
        let alias = Modops.strengthen_and_subst_module_body mp_from source mp false in
        let fields, inner_mp, subs =
          fields_of_signature Mod_subst.empty_subst mp [] (mod_type alias) in
        let subs =
          if ModPath.equal inner_mp mp then subs
          else Mod_subst.add_mp inner_mp mp (Mod_subst.empty_delta_resolver mp) subs
        in
        Modops.subst_structure subs mp fields
      | _ ->
        (* As vernac/assumptions.ml's [fields_of_mp]. *)
        let subs =
          if ModPath.equal inner_mp mp then subs
          else if Mod_subst.has_root_delta_resolver mp (mod_delta mb) then
            Mod_subst.add_mp inner_mp mp (Mod_subst.of_body_delta_resolver (mod_delta mb)) subs
          else Mod_subst.add_mp inner_mp mp (Mod_subst.empty_delta_resolver mp) subs
        in
        Modops.subst_structure subs mp raw_fields
    in
    let fields = index_fields fields in
    st.fields <- ModPath.Map.add mp fields st.fields;
    fields

and fields_of_mb st subs mp mb args = match mod_expr mb with
  | Algebraic me ->
    fields_of_functor (fields_of_expr st) subs mp args
      (Modops.annotate_module_expression me (mod_type mb))
  | Struct (_, struc) ->
    fields_of_signature subs mp args (Modops.annotate_struct_body struc (mod_type mb))
  | Abstract | FullStruct -> fields_of_signature subs mp args (mod_type mb)

and fields_of_signature subs mp args sign =
  fields_of_functor (fun subs mp0 args struc ->
      if not (List.is_empty args) then raise Not_found;
      (struc, mp0, subs))
    subs mp args sign

and fields_of_expr st subs mp0 args = function
  | MEident mp ->
    let mp = Mod_subst.subst_mp subs mp in
    fields_of_mb st subs mp (lookup_module_in_impl st mp) args
  | MEapply (me, mp) -> fields_of_expr st subs mp0 (mp :: args) me
  | MEwith _ -> raise Not_found (* no 'with' in an implementation *)

let in_impl st get kn =
  let mp, lab = KerName.repr kn in
  match fields_of_mp st mp with
  | fields -> get fields lab
  | exception Not_found -> None

(* A public term uses its final-environment declaration. When that declaration
   has no body, its proof witness is the implementation. A term already
   reached from an implementation keeps that implementation view. The user
   name, not its canonical target, selects a transparent Include alias. *)
let lookup_constant st view kn =
  let impl () = in_impl st find_constant (Constant.user kn) in
  match view with
  | Public ->
    if Environ.mem_constant kn st.env then
      let cb = Environ.lookup_constant kn st.env in
      if Declareops.constant_has_body cb then Some (Public, cb)
      else match impl () with
        | Some cb -> Some (Implementation, cb)
        | None -> Some (Public, cb)
    else Option.map (fun cb -> (Implementation, cb)) (impl ())
  | Implementation ->
    match impl () with
    | Some cb -> Some (Implementation, cb)
    | None ->
      if Environ.mem_constant kn st.env then Some (Public, Environ.lookup_constant kn st.env)
      else None

let lookup_mind st view mind =
  let impl () = in_impl st find_mind (MutInd.user mind) in
  match view with
  | Public ->
    if Environ.mem_mind mind st.env then Some (Public, Environ.lookup_mind mind st.env)
    else Option.map (fun mib -> (Implementation, mib)) (impl ())
  | Implementation ->
    match impl () with
    | Some mib -> Some (Implementation, mib)
    | None ->
      if Environ.mem_mind mind st.env then Some (Public, Environ.lookup_mind mind st.env)
      else None

(** {6 The objects a declaration mentions} *)

(* A hash of the top [depth] levels of a term, for the cache of [seen]. The
   walk asks [seen] about each compound node it reaches, so the hash must read
   a bounded number of nodes: a hash of the whole term at each of its nodes
   would make the walk quadratic in the size of the term. The depth is 3: the
   node, its subterms and theirs, so that two nodes with the same head (two
   applications, two products) still differ by what they apply or bind and
   by the names one level further down. A node contributes at most three
   subterms here ([LetIn]), so a hash reads at most 1 + 3 + 9 nodes. Nodes
   that agree on their top three levels share a slot and evict each other,
   which costs a second walk of a node and never changes a result: [seen]
   compares the terms themselves. *)
let hash_depth = 3

let rec bounded_hash depth c =
  let open Hashset.Combine in
  let sub c = if depth <= 1 then 0 else bounded_hash (depth - 1) c in
  match Constr.kind c with
  | Rel i -> combinesmall 1 i
  | Var id -> combinesmall 2 (Id.hash id)
  | Meta i -> combinesmall 3 i
  | Evar (e, _) -> combinesmall 4 (Evar.hash e)
  | Sort s -> combinesmall 5 (Sorts.hash s)
  | Cast (c, k, _) -> combinesmall 6 (combine (Constr.hash_cast_kind k) (sub c))
  | Prod (_, t, b) -> combinesmall 7 (combine (sub t) (sub b))
  | Lambda (_, t, b) -> combinesmall 8 (combine (sub t) (sub b))
  | LetIn (_, b, t, c) -> combinesmall 9 (combine3 (sub b) (sub t) (sub c))
  | App (f, args) ->
    let n = Array.length args in
    combinesmall 10 (combine3 (sub f) n (if Int.equal n 0 then 0 else sub args.(n - 1)))
  | Const (kn, _) -> combinesmall 11 (Constant.UserOrd.hash kn)
  | Ind (ind, _) -> combinesmall 12 (Ind.UserOrd.hash ind)
  | Construct (cstr, _) -> combinesmall 13 (Construct.UserOrd.hash cstr)
  | Case (ci, _, _, _, _, c, br) ->
    combinesmall 14 (combine3 (Ind.UserOrd.hash ci.ci_ind) (Array.length br) (sub c))
  | Fix ((_, i), (_, tl, _)) -> combinesmall 15 (combine i (Array.length tl))
  | CoFix (i, (_, tl, _)) -> combinesmall 16 (combine i (Array.length tl))
  | Proj (p, _, c) -> combinesmall 17 (combine (Projection.UserOrd.hash p) (sub c))
  | Int i -> combinesmall 18 (Uint63.hash i)
  | Float f -> combinesmall 19 (Float64.hash f)
  | String s -> combinesmall 20 (Pstring.hash s)
  | Array (_, t, _, _) -> combinesmall 21 (Array.length t)

(* A term is a graph with shared nodes, which a walk of its tree visits once
   per path: [seen] skips a node already walked in the same declaration. The
   cache is lossy and direct-mapped: a miss only walks the node again, and a
   hit needs the very node ([==]) of the same walk ([gen]), whose references
   that walk has already collected. *)
let cache_size = 1 lsl 18

let fresh_gen st = st.gen <- st.gen + 1; st.gen

let seen st gen c =
  let i = bounded_hash hash_depth c land (cache_size - 1) in
  if Int.equal st.gens.(i) gen && st.keys.(i) == c then true
  else begin
    st.gens.(i) <- gen;
    st.keys.(i) <- c;
    false
  end

let empty_refs = GlobRef.Set.empty, GlobRef.Set.empty

let add_ref view obj (public, implementation) = match view with
  | Public -> GlobRef.Set.add obj public, implementation
  | Implementation -> public, GlobRef.Set.add obj implementation

let add_mind view mind refs = add_ref view (GlobRef.IndRef (mind, 0)) refs

(* The primitive type a literal has, which the kernel looks up to type it. *)
let add_prim view prim refs = match prim with
  | Some c -> add_ref view (GlobRef.ConstRef c) refs
  | None -> refs

let refs_to_list (public, implementation) =
  List.map (fun obj -> Public, obj) (GlobRef.Set.elements public)
  @ List.map (fun obj -> Implementation, obj) (GlobRef.Set.elements implementation)

(* The walk keeps its own list of terms to visit, so its depth does not depend
   on the depth of the terms. A term retains the declaration view that typed
   it. The inductive of a [match] and of a projection, and the primitive type
   of a literal or an array, are objects the term relies on even though no
   subterm names them. *)
let rec walk st gen refs = function
  | [] -> refs
  | (view, c) :: todo ->
    let open Constr in
    let retro = Environ.retroknowledge st.env in
    match kind c with
    | Rel _ | Var _ | Sort _ | Meta _ | Evar _ -> walk st gen refs todo
    | Int _ -> walk st gen (add_prim view retro.Retroknowledge.retro_int63 refs) todo
    | Float _ -> walk st gen (add_prim view retro.Retroknowledge.retro_float64 refs) todo
    | String _ -> walk st gen (add_prim view retro.Retroknowledge.retro_string refs) todo
    | Const (kn, _) -> walk st gen (add_ref view (GlobRef.ConstRef kn) refs) todo
    | Ind ((mind, _), _) | Construct (((mind, _), _), _) ->
      walk st gen (add_mind view mind refs) todo
    | Cast _ | Prod _ | Lambda _ | LetIn _ | App _ | Proj _ | Case _ | Fix _ | CoFix _ | Array _ ->
      if seen st gen c then walk st gen refs todo
      else
        let refs = match kind c with
          | Case (ci, _, _, _, _, _, _) -> add_mind view (fst ci.ci_ind) refs
          | Proj (p, _, _) -> add_mind view (Projection.mind p) refs
          | Array _ -> add_prim view retro.Retroknowledge.retro_array refs
          | _ -> refs
        in
        walk st gen refs (fold (fun todo c -> (view, c) :: todo) todo c)

let push_context view ctx todo =
  List.fold_left (fun todo d ->
      Context.Rel.Declaration.fold_constr (fun c todo -> (view, c) :: todo) d todo)
    todo ctx

let typing_flags obj (tf : typing_flags) acc =
  let add ok kind acc = if ok then acc else (kind, obj) :: acc in
  acc
  |> add tf.check_universes "type-in-type"
  |> add tf.check_guarded "unsafe-fixpoint"
  |> add tf.check_eliminations "unchecked-eliminations"

(* The same test as vernac/assumptions.ml's [uses_uip]. *)
let uses_uip mib =
  Array.exists (fun mip ->
      Option.is_empty mip.mind_squashed
      && (match mip.mind_relevance with Sorts.Irrelevant -> true | _ -> false)
      && Int.equal (Array.length mip.mind_nf_lc) 1
      && Int.equal (List.length (fst mip.mind_nf_lc.(0))) (List.length mib.mind_params_ctxt))
    mib.mind_packets

let unresolved = { refs = []; axiom = true; flags = [] }

let constant_node st view kn =
  match lookup_constant st view kn with
  | None -> unresolved
  | Some (declaration_view, cb) ->
    (* An opaque body that cannot be read counts as an axiom: the proof rests
       on something this process cannot check. vernac/assumptions.ml lists
       such a constant apart from the axioms; the closure has axioms and
       flags only, and an unchecked body must not pass for no assumption.
       The warning names the constant and the reason the read failed. *)
    let body, axiom = match cb.const_body with
      | Def c -> [declaration_view, c], false
      | OpaqueDef o ->
        (match st.access o with
         | c, _ -> [declaration_view, c], false
         | exception e when CErrors.noncritical e ->
           Feedback.msg_warning
             Pp.(str "The opaque body of " ++ str (Constant.to_string kn)
                 ++ str " could not be read, so it counts as an axiom: " ++ CErrors.print e);
           [], true)
      | Undef _ | Primitive _ | Symbol _ -> [], true
    in
    let refs = walk st (fresh_gen st) empty_refs ((declaration_view, cb.const_type) :: body) in
    { refs = refs_to_list refs; axiom;
      flags = typing_flags (GlobRef.ConstRef kn) cb.const_typing_flags [] }

let mind_node st view mind =
  match lookup_mind st view mind with
  | None -> unresolved
  | Some (declaration_view, mib) ->
    let todo =
      Array.fold_left (fun todo mip ->
          push_context declaration_view mip.mind_arity_ctxt
            (Array.fold_left (fun todo c -> (declaration_view, c) :: todo) todo mip.mind_user_lc))
        (push_context declaration_view mib.mind_params_ctxt []) mib.mind_packets
    in
    let refs = walk st (fresh_gen st) empty_refs todo in
    (* A mutual block has one label but a name for each of its types, and
       the closure reports the block under its first inductive: the names of
       all its types are tested, for every block the closure resolves. *)
    Array.iter (fun mip ->
        if not (CheckNames.valid_id mip.mind_typename) then
          CErrors.user_err
            Pp.(str ("The axiom closure reached the inductive type name " ^
                     CheckNames.quote (Id.to_string mip.mind_typename) ^
                     ", which is not an identifier.")))
      mib.mind_packets;
    let name = GlobRef.IndRef (mind, 0) in
    let tf = mib.mind_typing_flags in
    let flags = typing_flags name tf [] in
    let add cond kind flags = if cond then (kind, name) :: flags else flags in
    let flags =
      flags
      |> add (not tf.check_positive) "assumed-positive"
      |> add (uses_uip mib) "uip"
      |> add (not tf.indices_matter
              && Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) mib.mind_packets)
        "indices-not-mattering"
    in
    { refs = refs_to_list refs; axiom = false; flags }

let node st view obj =
  let nodes = match view with
    | Public -> st.public_nodes
    | Implementation -> st.implementation_nodes
  in
  match GlobRef.Map.find_opt obj nodes with
  | Some n -> n
  | None ->
    let n = match obj with
      | GlobRef.ConstRef kn -> constant_node st view kn
      | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> mind_node st view mind
      | GlobRef.VarRef _ -> { refs = []; axiom = false; flags = [] }
    in
    begin match view with
    | Public -> st.public_nodes <- GlobRef.Map.add obj n st.public_nodes
    | Implementation -> st.implementation_nodes <- GlobRef.Map.add obj n st.implementation_nodes
    end;
    n

let name_of = function
  | GlobRef.ConstRef kn -> Constant.to_string kn
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> MutInd.to_string mind
  | GlobRef.VarRef id -> Id.to_string id

(* The comparator compares the printed name of each axiom with the names its
   config permits (checkNames.mli), so a name that is not made of identifiers
   is refused. Each object whose name [axioms_and_flags] returns is tested
   when the closure reaches it, as are the type names of each inductive block
   it resolves ([mind_node]). *)
let check_printed_name obj =
  let valid = match obj with
    | GlobRef.ConstRef kn -> CheckNames.valid_kername (Constant.user kn)
    | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
      CheckNames.valid_kername (MutInd.user mind)
    | GlobRef.VarRef id -> CheckNames.valid_id id
  in
  if not valid then
    CErrors.user_err
      Pp.(str ("The axiom closure reached the name " ^ CheckNames.quote (name_of obj) ^
               ", which is not made of identifiers."))

module FlagSet = Stdlib.Set.Make (struct
    type t = string * GlobRef.t
    let compare (k1, o1) (k2, o2) =
      let c = String.compare k1 k2 in
      if Int.equal c 0 then GlobRef.UserOrd.compare o1 o2 else c
  end)

(** The axioms and flags of every object reachable from [root]. The axioms
    are the objects themselves, not their printed names: two objects can
    print the same name (a constant [Q.g] of a module [Q] of the library
    [R.P] prints as the constant [g] of the library [R.P.Q]), and the
    comparator must tell them apart. A name that is not made of identifiers
    stops the walk ([check_printed_name]). *)
let closure st root =
  let rec loop public_seen implementation_seen axioms flags = function
    | [] -> axioms, flags
    | (view, obj) :: todo ->
      let seen = match view with
        | Public -> GlobRef.Set.mem obj public_seen
        | Implementation -> GlobRef.Set.mem obj implementation_seen
      in
      if seen then loop public_seen implementation_seen axioms flags todo
      else
        let n = node st view obj in
        if n.axiom || not (List.is_empty n.flags) then check_printed_name obj;
        let axioms = if n.axiom then GlobRef.Set.add obj axioms else axioms in
        let flags = List.fold_left (fun flags f -> FlagSet.add f flags) flags n.flags in
        let public_seen, implementation_seen = match view with
          | Public -> GlobRef.Set.add obj public_seen, implementation_seen
          | Implementation -> public_seen, GlobRef.Set.add obj implementation_seen
        in
        loop public_seen implementation_seen axioms flags (List.rev_append n.refs todo)
  in
  loop GlobRef.Set.empty GlobRef.Set.empty GlobRef.Set.empty FlagSet.empty [Public, root]

(** {6 Entry points} *)

(* The comparator asks for several constants in one run, so the walk's caches
   are built once and kept. *)
let closure_state env access = {
  env; access; fields = ModPath.Map.empty;
  public_nodes = GlobRef.Map.empty; implementation_nodes = GlobRef.Map.empty; gen = 0;
  keys = Array.make cache_size Constr.mkProp; gens = Array.make cache_size (-1);
}

let axioms_and_flags st kn =
  let axioms, flags = closure st (GlobRef.ConstRef kn) in
  let axioms = List.map (fun obj -> name_of obj, obj) (GlobRef.Set.elements axioms) in
  let flags =
    List.map (fun (kind, obj) -> kind, name_of obj, obj) (FlagSet.elements flags)
    |> List.stable_sort (fun (k1, n1, _) (k2, n2, _) ->
        let c = String.compare k1 k2 in if Int.equal c 0 then String.compare n1 n2 else c)
  in
  List.stable_sort (fun (a, _) (b, _) -> String.compare a b) axioms, flags
