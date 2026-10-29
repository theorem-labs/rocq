(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The statement report of [rocqchk -statement-report FILE]: for each
    request, whether a constant has the type of another one, and the axioms
    and relaxed typing flags the first one rests on.

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

(** {6 Requests} *)

type request = {
  req_name : string;
  req_model : string;
  req_trusted : string option;
}

let usage_error file lineno =
  CErrors.user_err
    Pp.(str "-statement-report: line " ++ int lineno ++ str " of " ++ str file ++
        str " is not `<name> <model-constant> [<trusted-constant>|-]`.")

(* Tokens are separated by single spaces: two spaces in a row make an empty
   token, which is refused, so no token can contain a space. *)
let parse_line file lineno line =
  let tokens = String.split_on_char ' ' line in
  if List.exists (fun t -> String.equal t "") tokens then usage_error file lineno;
  match tokens with
  | [name; model] | [name; model; "-"] ->
    { req_name = name; req_model = model; req_trusted = None }
  | [name; model; trusted] ->
    { req_name = name; req_model = model; req_trusted = Some trusted }
  | _ -> usage_error file lineno

let read_requests file =
  let ch =
    try open_in file
    with Sys_error msg ->
      CErrors.user_err Pp.(str "-statement-report: cannot read " ++ str file ++ str ": " ++ str msg)
  in
  let rec loop lineno acc =
    match input_line ch with
    | exception End_of_file -> List.rev acc
    | line ->
      if String.exists (fun c -> c = '\t' || c = '\r') line then usage_error file lineno;
      if String.equal line "" || line.[0] = '#' then loop (lineno + 1) acc
      else loop (lineno + 1) (parse_line file lineno line :: acc)
  in
  Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () -> loop 1 [])

(** {6 Implementations hidden by module signatures}

    The report resolves a term in the declaration view that typed it. A public
    declaration uses its environment view; a bodyless public declaration falls
    back to its implementation and then follows that implementation's fields.
    This prevents an independent signature proof from replacing a proof
    witness that depends on a relaxed kernel check. *)

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
type state = {
  env : Environ.env;
  access : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm;
  mutable fields : field_index ModPath.Map.t;
  (* the indexed fields of the implementation of each module looked up so far *)
  mutable public_nodes : node GlobRef.Map_env.t;
  mutable implementation_nodes : node GlobRef.Map_env.t;
  (* each object reached so far, keyed by its constant or by the first
     inductive of its block, in the declaration view that typed its use *)
  mutable gen : int;
  keys : Constr.t array;
  gens : int array;
  (* the cache of [seen] *)
}

and node = {
  refs : vref list;
  (* the objects the selected declaration mentions, with the view that
     typed each reference *)
  axiom : bool;
  (* no body: a constant without one, an opaque constant whose body cannot be
     read, or an object neither the environment nor an implementation
     resolves, which is reported rather than left out *)
  flags : (string * string) list;
  (* the relaxed typing conditions the selected object relies on,
     (kind, object) *)
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

(* As in vernac/assumptions.ml (#22533): a module whose parent's
   implementation cannot be read is taken from the environment, which holds
   its signature. *)
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
        let subs =
          if ModPath.equal inner_mp mp then subs
          else if Mod_subst.has_root_delta_resolver mp (mod_delta mb) then
            Mod_subst.add_mp inner_mp mp (mod_delta mb) subs
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

(* A term is a graph with shared nodes: [seen] skips a node already walked in
   the same declaration, as vernac/assumptions.ml does, with a cache of the
   same size. The cache is lossy and direct-mapped: a miss only walks the node
   again. *)
let cache_size = 1 lsl 18

let fresh_gen st = st.gen <- st.gen + 1; st.gen

let seen st gen c =
  let i = Constr.hash_bounded c land (cache_size - 1) in
  if Int.equal st.gens.(i) gen && st.keys.(i) == c then true
  else begin
    st.gens.(i) <- gen;
    st.keys.(i) <- c;
    false
  end

let empty_refs = GlobRef.Set_env.empty, GlobRef.Set_env.empty

let add_ref view obj (public, implementation) = match view with
  | Public -> GlobRef.Set_env.add obj public, implementation
  | Implementation -> public, GlobRef.Set_env.add obj implementation

let add_mind view mind refs = add_ref view (GlobRef.IndRef (mind, 0)) refs

(* The primitive type a literal has, which the kernel looks up to type it. *)
let add_prim view prim refs = match prim with
  | Some c -> add_ref view (GlobRef.ConstRef c) refs
  | None -> refs

let refs_to_list (public, implementation) =
  List.map (fun obj -> Public, obj) (GlobRef.Set_env.elements public)
  @ List.map (fun obj -> Implementation, obj) (GlobRef.Set_env.elements implementation)

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

let typing_flags name (tf : typing_flags) acc =
  let add ok kind acc = if ok then acc else (kind, name) :: acc in
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

(* Test-only seam, beside [test_fault] below: a test sets this to make the
   opaque accessor fail for one constant, so the unreadable-body warning has a
   test without a damaged .vo. The real failures it stands for — a proof stored
   nowhere, and a lazy reader refusing a table whose bytes changed since intern
   — are not reachable from this test suite's own objects. *)
let test_unreadable_opaque kn =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE" with
  | Some c when String.equal c (Constant.to_string kn) ->
    CErrors.user_err Pp.(str "test unreadable opaque body")
  | None | Some _ -> ()

let constant_node st view kn =
  match lookup_constant st view kn with
  | None -> unresolved
  | Some (declaration_view, cb) ->
    (* An opaque body that cannot be read is reported as an axiom, as
       vernac/assumptions.ml's [get_constant_body] does: a constant whose body
       this process cannot see rests on something it cannot check. The read can
       fail for two unrelated reasons, though — the proof was not stored, which
       is what upstream means, or the table could not be READ (damaged bytes, or
       a lazy reader refusing a table whose bytes changed since intern) — and
       the verdict alone does not tell them apart. So the failure is named here.
       The exit status is deliberately unchanged: a stored-nowhere body is an
       ordinary answer, and failing the whole check on it would turn every
       delayed proof into a failed grade. A reader who needs certainty reads the
       warning, which names the constant. *)
    let body, axiom = match cb.const_body with
      | Def c -> [declaration_view, c], false
      | OpaqueDef o ->
        (match (test_unreadable_opaque kn; st.access o) with
         | c, _ -> [declaration_view, c], false
         | exception e when CErrors.noncritical e ->
           Feedback.msg_warning
             Pp.(str "Statement report: the opaque body of " ++ str (Constant.to_string kn)
                 ++ str " could not be read, so it is reported as an axiom: " ++ CErrors.print e);
           [], true)
      | Undef _ | Primitive _ | Symbol _ -> [], true
    in
    let refs = walk st (fresh_gen st) empty_refs ((declaration_view, cb.const_type) :: body) in
    { refs = refs_to_list refs; axiom;
      flags = typing_flags (Constant.to_string kn) cb.const_typing_flags [] }

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
    Array.iter (fun mip ->
        if not (CheckNames.valid_id mip.mind_typename) then
          CErrors.user_err
            Pp.(str ("The statement report reached the inductive type name " ^
                     CheckNames.quote (Id.to_string mip.mind_typename) ^
                     ", which is not an identifier.")))
      mib.mind_packets;
    let name = MutInd.to_string mind in
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
  match GlobRef.Map_env.find_opt obj nodes with
  | Some n -> n
  | None ->
    let n = match obj with
      | GlobRef.ConstRef kn -> constant_node st view kn
      | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> mind_node st view mind
      | GlobRef.VarRef _ -> { refs = []; axiom = false; flags = [] }
    in
    begin match view with
    | Public -> st.public_nodes <- GlobRef.Map_env.add obj n st.public_nodes
    | Implementation -> st.implementation_nodes <- GlobRef.Map_env.add obj n st.implementation_nodes
    end;
    n

let name_of = function
  | GlobRef.ConstRef kn -> Constant.to_string kn
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> MutInd.to_string mind
  | GlobRef.VarRef id -> Id.to_string id

(* Place 2 of the name check (checkNames.mli), for a name that the check at
   load cannot see: a constant or an inductive that a term of an admitted
   library names and that no library declares, which the report prints as an
   axiom. Each object whose name an [axiom] or [flag] line would print is
   tested when the closure reaches it, as are the type names of each inductive
   block it resolves ([mind_node]). This is before the statement's line, so a
   refusal leaves no END STATEMENT REPORT line. It is after the type verdicts:
   [print] decides every verdict before the first statement line, and a
   verdict's conversion can reach an anomaly that prints an unresolved
   inductive's name. That anomaly stops the report before its first statement
   line, and the warning of coqchk_main.ml escapes its text. *)
let check_printed_name obj =
  let valid = match obj with
    | GlobRef.ConstRef kn -> CheckNames.valid_kername (Constant.user kn)
    | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
      CheckNames.valid_kername (MutInd.user mind)
    | GlobRef.VarRef id -> CheckNames.valid_id id
  in
  if not valid then
    CErrors.user_err
      Pp.(str ("The statement report would print the name " ^ CheckNames.quote (name_of obj) ^
               ", which is not made of identifiers."))

module FlagSet = Stdlib.Set.Make (struct
    type t = string * string
    let compare (k1, o1) (k2, o2) =
      let c = String.compare k1 k2 in
      if Int.equal c 0 then String.compare o1 o2 else c
  end)

(** The axioms and flags of every object reachable from [root]. A name the
    report must not print stops it ([check_printed_name]). *)
let closure st root =
  let rec loop public_seen implementation_seen axioms flags = function
    | [] -> axioms, flags
    | (view, obj) :: todo ->
      let seen = match view with
        | Public -> GlobRef.Set_env.mem obj public_seen
        | Implementation -> GlobRef.Set_env.mem obj implementation_seen
      in
      if seen then loop public_seen implementation_seen axioms flags todo
      else
        let n = node st view obj in
        if n.axiom || not (List.is_empty n.flags) then check_printed_name obj;
        let axioms = if n.axiom then CString.Set.add (name_of obj) axioms else axioms in
        let flags = List.fold_left (fun flags f -> FlagSet.add f flags) flags n.flags in
        let public_seen, implementation_seen = match view with
          | Public -> GlobRef.Set_env.add obj public_seen, implementation_seen
          | Implementation -> public_seen, GlobRef.Set_env.add obj implementation_seen
        in
        loop public_seen implementation_seen axioms flags (List.rev_append n.refs todo)
  in
  loop GlobRef.Set_env.empty GlobRef.Set_env.empty CString.Set.empty FlagSet.empty [Public, root]

(** {6 The type match} *)

(* The universe comparison that checking [Definition f := model] against a
   monomorphic [Parameter f : <type>] of a sealing module type makes (the
   inference mode of kernel/subtyping.ml's [check_constant]): a comparison that
   does not hold yet adds the constraints it needs, if they are consistent with
   the environment. The state is a pair: the universe graph with those
   constraints, and the set of those constraints alone, which is what the
   sealing adds to the global universes. A graph cannot be diffed or unioned,
   so the set is kept beside it. The error marks a needed constraint that is
   inconsistent. *)
let infer_universes : (UGraph.t * Univ.UnivConstraints.t, unit) Conversion.universe_compare =
  let merge csts (g, added) =
    match UGraph.merge_constraints csts g with
    | g -> Result.Ok (g, Univ.UnivConstraints.union csts added)
    | exception UGraph.UniverseInconsistency _ -> Result.Error (Some ())
  in
  let leq u v (g, added) =
    match UGraph.enforce_leq_alg u v g with
    | csts, g -> Result.Ok (g, Univ.UnivConstraints.union csts added)
    | exception UGraph.UniverseInconsistency _ -> Result.Error (Some ())
  in
  let compare_sorts pb s1 s2 (g, _ as state) =
    let holds = match pb with
      | Conversion.CUMUL -> UGraph.check_leq_sort Sorts.Quality.equal g s1 s2
      | Conversion.CONV -> UGraph.check_eq_sort Sorts.Quality.equal g s1 s2
    in
    if holds then Result.Ok state
    (* As pretyping/reductionops.ml's [Infer]: the qualities must already
       compare, and only the universe constraint is inferred. The checked
       comparison above has decided every case with an impredicative sort. *)
    else match s1, s2 with
      | (Sorts.SProp | Sorts.Prop), _ | _, (Sorts.SProp | Sorts.Prop) -> Result.Error None
      | _ when not (Sorts.Quality.equal (Sorts.quality s1) (Sorts.quality s2)) -> Result.Error None
      | _ ->
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        match pb with
        | Conversion.CUMUL -> leq u1 u2 state
        | Conversion.CONV ->
          (* As engine/univSubst.ml's [enforce_eq]: only two levels can be made equal. *)
          match Univ.Universe.level u1, Univ.Universe.level u2 with
          | Some _, Some _ -> Result.bind (leq u1 u2 state) (leq u2 u1)
          | _ -> Result.Error (Some ())
  in
  let compare_instances ~flex u1 u2 (g, _ as state) =
    if UGraph.check_eq_instances Sorts.Quality.equal g u1 u2 then Result.Ok state
    else if flex then Result.Error None
    else
      let qcsts, ucsts = UVars.enforce_eq_instances u1 u2 UVars.empty_unif_constraints in
      if UVars.QUnifConstraints.is_trivial qcsts then merge ucsts state else Result.Error None
  in
  let compare_cumul_instances pb variances u1 u2 state =
    let qcsts, ucsts = Conversion.get_cumulativity_constraints pb variances u1 u2 in
    if UVars.QUnifConstraints.is_trivial qcsts then merge ucsts state else Result.Error None
  in
  { Conversion.compare_sorts; compare_instances; compare_cumul_instances }

(* What the sealing of a model that reads [match] adds to the global
   universes: [fresh] universes strictly above Set, the instance it declares
   for a polymorphic model ([Univ.Level.var 0] to [fresh - 1] in
   [constraints]), and the constraints its comparison needed. For a
   polymorphic model this is complete only because [type_verdict] compares
   no model whose universe context has constraints: such a context's own
   constraints would be in the comparison's graph but not in [constraints]. *)
type sealing = { fresh : int; constraints : Univ.UnivConstraints.t }

let adds_nothing = { fresh = 0; constraints = Univ.UnivConstraints.empty }

(* Whether the model constant can stand for the trusted constant in a module
   sealed by a signature that declares the trusted type T: whether [Definition
   f := model] ([Polymorphic] when T is) is accepted for the field [Parameter f
   : T] (kernel/subtyping.ml's [check_constant]). The model's type must be
   cumulative to T. Against a monomorphic T, a needed universe constraint is
   added when it is consistent with the environment; against a polymorphic T,
   the definition's universe context must be T's and adds no constraint.
   Elaborating the definition takes a polymorphic model at fresh universes,
   and can minimize them when the model's universe context has sort variables
   or constraints; this check does not replay that, so it answers
   [universes-differ] for such a model, which the sealing may still accept.
   [Ok] is [match], with what the sealing adds to the global universes;
   [Error] is any other verdict. *)
let type_verdict env model trusted : (sealing, string) result =
  let cm = Environ.lookup_constant model env and ct = Environ.lookup_constant trusted env in
  let infer ~fresh env =
    let state = (Environ.universes env, Univ.UnivConstraints.empty), infer_universes in
    match Conversion.generic_conv Conversion.CUMUL ~l2r:false TransparentState.full env state
            cm.const_type ct.const_type with
    | Result.Ok (_, constraints) -> Ok { fresh; constraints }
    | Result.Error None -> Error "mismatch"
    | Result.Error (Some ()) -> Error "universes-differ"
  in
  (* The definition's context [am] must be T's context [at]; the types are
     compared under [at]. A failure that ignoring universe levels removes needs a
     constraint that [at] does not give. *)
  let against_polymorphic am at =
    if Subtyping.check_polymorphic_universes env at am then
      let env = Environ.push_context ~strict:false (UVars.AbstractContext.repr at) env in
      match Conversion.default_conv_leq env cm.const_type ct.const_type with
      | Result.Ok () -> Ok adds_nothing
      | Result.Error () ->
        match Conversion.default_conv_leq (Environ.set_type_in_type true env)
                cm.const_type ct.const_type with
        | Result.Ok () -> Error "universes-differ"
        | Result.Error () -> Error "mismatch"
    else Error "universes-differ"
  in
  let minimizable am =
    fst (UVars.AbstractContext.size am) > 0
    || not (PConstraints.is_empty (UVars.UContext.constraints (UVars.AbstractContext.repr am)))
  in
  match cm.const_universes, ct.const_universes with
  | Monomorphic, Monomorphic -> infer ~fresh:0 env
  | Monomorphic, Polymorphic at -> against_polymorphic UVars.AbstractContext.empty at
  | Polymorphic am, _ when minimizable am -> Error "universes-differ"
  | Polymorphic am, Monomorphic ->
    (* The model's bound universes are fresh in [env]: they are its instance. The
       definition declares them as global universes, which [Global.push_context_set]
       does with [~strict:true], so each is above [Set] and cannot be taken as it.
       The arm above leaves [am] without constraints, so the sealing adds only
       these fresh universes and the comparison's constraints; relaxing that arm
       would leave the context's own constraints out of the sealing. *)
    infer ~fresh:(snd (UVars.AbstractContext.size am))
      (Environ.push_context ~strict:true (UVars.AbstractContext.repr am) env)
  | Polymorphic am, Polymorphic at -> against_polymorphic am at

(* Whether the sealings can be loaded together. One rocqchk run over the
   libraries of all the sealings loads them at once, each adding its
   constraints to the global universes, so constraints that are consistent
   with the environment one sealing at a time must also be consistent
   together. Each sealing declares its own fresh universes: they are renamed
   apart. The answer does not depend on the order of [sealings]. *)
let load_together env sealings =
  let add (g, next) { fresh; constraints } =
    let rename l = match Univ.Level.var_index l with
      | Some i -> Univ.Level.var (next + i)
      | None -> l
    in
    let rec declare g i =
      if Int.equal i fresh then g
      else declare (UGraph.add_universe (Univ.Level.var (next + i)) ~strict:true g) (i + 1)
    in
    let constraints =
      Univ.UnivConstraints.fold (fun (u, d, v) acc ->
          Univ.UnivConstraints.add (rename u, d, rename v) acc)
        constraints Univ.UnivConstraints.empty
    in
    UGraph.merge_constraints constraints (declare g 0), next + fresh
  in
  match List.fold_left add (Environ.universes env, 0) sealings with
  | _ -> true
  | exception UGraph.UniverseInconsistency _ -> false

(** {6 The report} *)

(* One message per line, so that a long report never builds one [Pp.t]. *)
let line fmt = Printf.ksprintf (fun s -> Feedback.msg_notice (Pp.str s)) fmt

(* Test-only seam: a test sets this for one process to exercise the public
   incomplete-report contract. It has no effect unless the test variable is
   explicitly set. *)
let test_fault () =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_FAILURE" with
  | Some "1" -> CErrors.user_err Pp.(str "test statement-report failure")
  | None | Some _ -> ()

(* Every verdict is decided before the first statement is printed: when the
   sealings of the statements that read [match] cannot be loaded together, the
   report stops with no statement line. A reader keeps each statement that the
   next statement line closes, so every statement printed before the stop but
   the last would still count. Like rocqchk's refusal to load those sealings,
   the stop takes every statement of the report with it, whatever their
   verdicts. The message of that stop gives the position among the requests of
   each statement that reads [match], never a name. The warning that prints it
   escapes it (coqchk_main.ml), so a name in it could no longer break the line
   and put a statement line back into a refused report; without names, the
   message does not rest on that escaping, and its whole line is the same
   whatever the requests and the libraries name. *)
let print env access requests =
  let index =
    Environ.fold_constants (fun c _ acc -> CString.Map.add (Constant.to_string c) c acc)
      env CString.Map.empty
  in
  let st = {
    env; access; fields = ModPath.Map.empty;
    public_nodes = GlobRef.Map_env.empty; implementation_nodes = GlobRef.Map_env.empty; gen = 0;
    keys = Array.make cache_size Constr.mkProp; gens = Array.make cache_size (-1);
  } in
  line "STATEMENT REPORT";
  test_fault ();

  let judged = List.map (fun r ->
      let model = CString.Map.find_opt r.req_model index in
      let verdict = match model, r.req_trusted with
        | None, _ -> Error "model-missing"
        | Some _, None -> Error "not-requested"
        | Some model, Some t ->
          match CString.Map.find_opt t index with
          | None -> Error "trusted-missing"
          | Some t -> type_verdict env model t
      in
      (* Only [Ok] reads match, with what its sealing adds: a verdict string
         match on the [Error] side would escape the check that the sealings
         load together. Every other verdict passes here, and
         misc/statement_report_sealing.sh asks for a report with each of them,
         so a new verdict that reads match on this side stops that report. *)
      (match verdict with
       | Error "match" -> CErrors.anomaly Pp.(str "statement report: match without its sealing.")
       | Ok _ | Error _ -> ());
      r, model, verdict)
      requests
  in
  (* The position of each statement that reads [match] among the requests,
     counted from 1, with what its sealing adds. *)
  let sealings = List.map_filter_i (fun i (_, _, verdict) ->
      Option.map (fun s -> i + 1, s) (Result.to_option verdict)) judged
  in
  if not (load_together env (List.map snd sealings)) then begin
    let positions = String.concat ", " (List.map (fun (i, _) -> string_of_int i) sealings) in
    CErrors.user_err (Pp.str (Printf.sprintf
      "the %d statements that read match (requests %s) need universe constraints \
       that are inconsistent together, so their sealings cannot all be loaded"
      (List.length sealings) positions))
  end;
  List.iter (fun (r, model, verdict) ->
      let verdict = match verdict with Ok _ -> "match" | Error v -> v in
      let trusted = Option.default "-" r.req_trusted in
      match model with
      | None -> line "statement %s %s %s %s 0 0" r.req_name r.req_model trusted verdict
      | Some model ->
        let axioms, flags = closure st (GlobRef.ConstRef model) in
        line "statement %s %s %s %s %d %d" r.req_name r.req_model trusted verdict
          (CString.Set.cardinal axioms) (FlagSet.cardinal flags);
        CString.Set.iter (line "axiom %s %s" r.req_name) axioms;
        FlagSet.iter (fun (kind, obj) -> line "flag %s %s %s" r.req_name kind obj) flags)
    judged;
  line "END STATEMENT REPORT"
