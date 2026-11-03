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
  resolved : bool;
  (* a constant the final environment holds without a body, reached in the
     public view and read through its implementation instead *)
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
      (* When the expression resolves to another module [M] (an alias
         [Module A := M], or an identity functor applied to [M]), [A] takes
         [M]'s strengthened signature. When it resolves to a functor's own
         body ([Module A := F X], sealed or not), there is no module to
         strengthen: the fields are the functor body's under the argument
         substitution, as vernac/assumptions.ml reads them, so that a field
         resolves to the body that defines it. *)
      let source = match mod_expr mb, ModPath.equal inner_mp mp with
        | Algebraic _, false ->
          let source = lookup_module_in_impl st inner_mp in
          (match mod_type source with NoFunctor _ -> Some source | MoreFunctor _ -> None)
        | _ -> None
      in
      match source with
      | Some source ->
        let mp_from = inner_mp in
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

let unresolved = { refs = []; axiom = true; flags = []; resolved = false }

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
    let resolved = match view, declaration_view with
      | Public, Implementation ->
        (* only a field the implementation defines: an axiom read there is
           still an axiom, not a resolution *)
        Environ.mem_constant kn st.env && Declareops.constant_has_body cb
      | _ -> false
    in
    { refs = refs_to_list refs; axiom; resolved;
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
    { refs = refs_to_list refs; axiom = false; flags; resolved = false }

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
      | GlobRef.VarRef _ -> { refs = []; axiom = false; flags = []; resolved = false }
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

(* The kernel name of the object the walk reached, whatever path it was reached
   by. A term names a constant by a pair of kernel names, user and canonical,
   and the environment is keyed by the user half alone, so nothing checks that
   a term's canonical half is the one its constant is stored under: a library
   could name [Evil.ax] with the canonical half [Allowed.ax]. So the canonical
   printed for an object the final environment holds is the canonical half of
   the key it is stored under there ([Environ.lookup_constant_key]); only an object
   that only an implementation holds is printed by the term's own pair. Two
   paths to one constant give one canonical name.

   It is printed so that two kernel names never print alike: the root of the
   module path, then [:], then the modules under it and the label, separated
   by dots. The root is the library's dirpath ([P.A:B.ax] is the constant [ax]
   of module [B] of library [P.A]; [P.A.B:ax] is the constant [ax] of library
   [P.A.B]), or, for a functor argument or a bound module, its unique form
   [<dirpath#name#n>]. No identifier contains [:], [<] or [#], so the string
   reads back to one kernel name. *)
let canonical_kername kn =
  let rec root acc = function
    | ModPath.MPfile dp -> DirPath.to_string dp, acc
    | ModPath.MPbound mbid -> MBId.debug_to_string mbid, acc
    | ModPath.MPdot (mp, l) -> root (Label.to_string l :: acc) mp
  in
  let mp, l = KerName.repr kn in
  let r, mods = root [] mp in
  r ^ ":" ^ String.concat "." (mods @ [Label.to_string l])

(* The canonical kernel name printed for [obj]; the name check reads the same
   one ([printable_name]). *)
let canonical_kn env = function
  | GlobRef.ConstRef kn ->
    if Environ.mem_constant kn env then
      let _, _, can = Environ.lookup_constant_key kn env in Some can
    else Some (Constant.canonical kn)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    if Environ.mem_mind mind env then
      let _, _, can = Environ.lookup_mind_key mind env in Some can
    else Some (MutInd.canonical mind)
  | GlobRef.VarRef _ -> None

let canonical_of st obj =
  match canonical_kn st.env obj with Some kn -> canonical_kername kn | None -> "-"

(* An [axiom] line's two names: the path the term reached the object by, then
   its canonical kernel name. *)
let axiom_entry st obj = name_of obj ^ " " ^ canonical_of st obj

module FlagSet = Stdlib.Set.Make (struct
    type t = string * string
    let compare (k1, o1) (k2, o2) =
      let c = String.compare k1 k2 in
      if Int.equal c 0 then String.compare o1 o2 else c
  end)

(* What a closure reports: its [axiom] entries, its [resolved] entries (each
   "<field> <canonical>") and its flags. *)
type closure_sets = {
  axioms : CString.Set.t;
  resolved_fields : CString.Set.t;
  flag_set : FlagSet.t;
}

let empty_sets = { axioms = CString.Set.empty; resolved_fields = CString.Set.empty; flag_set = FlagSet.empty }

let union_sets a b = {
  axioms = CString.Set.union a.axioms b.axioms;
  resolved_fields = CString.Set.union a.resolved_fields b.resolved_fields;
  flag_set = FlagSet.union a.flag_set b.flag_set;
}

let sets_size c =
  CString.Set.cardinal c.axioms + CString.Set.cardinal c.resolved_fields + FlagSet.cardinal c.flag_set

(* What a node itself adds to its closure. *)
let node_sets st n obj = {
  axioms = if n.axiom then CString.Set.singleton (axiom_entry st obj) else CString.Set.empty;
  resolved_fields = if n.resolved then CString.Set.singleton (axiom_entry st obj) else CString.Set.empty;
  flag_set = List.fold_left (fun s f -> FlagSet.add f s) FlagSet.empty n.flags;
}

(* Place 2 of the name check (checkNames.mli), for a name that the check at
   load cannot see: a constant or an inductive that a term of an admitted
   library names and that no library declares, which the report prints as an
   axiom. Each object whose name an [axiom] or [flag] line would print is
   tested when the closure reaches it, as are the type names of each inductive
   block it resolves ([mind_node]). This is before the type verdict, whose
   conversion can reach an anomaly that prints an unresolved inductive's name,
   and before the statement's line, so a refusal leaves no END STATEMENT
   REPORT line. *)
let printable_name env obj =
  let canonical_ok () = match canonical_kn env obj with
    | Some kn -> CheckNames.valid_kername kn
    | None -> true
  in
  match obj with
  | GlobRef.ConstRef kn -> CheckNames.valid_kername (Constant.user kn) && canonical_ok ()
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    CheckNames.valid_kername (MutInd.user mind) && canonical_ok ()
  | GlobRef.VarRef id -> CheckNames.valid_id id

let check_printed_name env obj =
  if not (printable_name env obj) then
    CErrors.user_err
      Pp.(str ("The statement report would print the name " ^ CheckNames.quote (name_of obj) ^
               ", which is not made of identifiers."))


(* Test-only seam, beside [test_fault] below: how many objects the report's
   walks entered, counted where an object is first reached rather than found
   already done. A report of [r] requests that shares one walk counts about
   the size of the union of their closures; one walk for each request counts
   about [r] times that. [COQ_TEST_SUITE_STATEMENT_REPORT_WALK] prints it. *)
let walk_visits = ref 0

(** The axioms and flags of every object reachable from [root], walked for
    that root alone. A name the report must not print stops it
    ([check_printed_name]). *)
let closure_per_root st root =
  let rec loop public_seen implementation_seen acc = function
    | [] -> acc
    | (view, obj) :: todo ->
      let seen = match view with
        | Public -> GlobRef.Set_env.mem obj public_seen
        | Implementation -> GlobRef.Set_env.mem obj implementation_seen
      in
      if seen then loop public_seen implementation_seen acc todo
      else
        let n = node st view obj in
        incr walk_visits;
        if n.axiom || n.resolved || not (List.is_empty n.flags) then check_printed_name st.env obj;
        let acc = union_sets (node_sets st n obj) acc in
        let public_seen, implementation_seen = match view with
          | Public -> GlobRef.Set_env.add obj public_seen, implementation_seen
          | Implementation -> public_seen, GlobRef.Set_env.add obj implementation_seen
        in
        loop public_seen implementation_seen acc (List.rev_append n.refs todo)
  in
  loop GlobRef.Set_env.empty GlobRef.Set_env.empty empty_sets [Public, root]

(** {6 One walk for every request}

    A root's answer is the union, over the objects the root reaches, of what
    each object itself declares: its name when it is an axiom, and its relaxed
    typing flags. Nothing in it depends on which root the walk started from.
    So the sub-closure of an object is worth keeping, and a report of [r]
    requests over one tree costs one pass over the union of their closures
    instead of [r] passes.

    [r] is not small in the runs this checker grades: a vendor-v21 production
    grade asks for 479 to 7,594 statements over one tree, 1,472 at the median
    of 66 such grades (dispatch://INFRA-167, the DeepCoqchk reading). The sets
    a node unions are small in the same grades: a statement's whole closure
    reports 14 axioms and a handful of flags.

    Correctness rests on two things, and the walk gives up and falls back to
    [closure_per_root] rather than guess at either:

    - The reference graph must be well founded, apart from the self reference
      of an inductive block, whose constructor types name the block. A body
      names only objects declared before it, so no other cycle can arise; a
      cycle all the same raises [Not_shareable].
    - A name the report must not print must stop the report where it stops it
      today. The shared walk reaches objects in the same order as
      [closure_per_root] (see [push_refs]), so the first such name is the same
      one; it raises [Not_shareable] and lets [closure_per_root] report it, so
      the error text comes from the same code as before.

    The memo holds one pair of sets for each object reached. [budget] bounds
    the elements it may hold, so a tree with far more axioms than these grades
    carry falls back instead of growing the heap without bound. *)

exception Not_shareable

type memo = {
  mutable public_closure : closure_sets GlobRef.Map_env.t;
  mutable implementation_closure : closure_sets GlobRef.Map_env.t;
  mutable pending_public : GlobRef.Set_env.t;
  mutable pending_implementation : GlobRef.Set_env.t;
  mutable budget : int;
  (* Set once a walk gave up: every later request takes [closure_per_root]. *)
  mutable shareable : bool;
}

(* The elements the memo may hold. 2^22 is far above what one of these trees
   needs (14 axioms over about 10^5 objects) and small enough that the memo
   cannot be the reason a checker runs out of memory. *)
let memo_budget = 1 lsl 22

let new_memo () = {
  public_closure = GlobRef.Map_env.empty;
  implementation_closure = GlobRef.Map_env.empty;
  pending_public = GlobRef.Set_env.empty;
  pending_implementation = GlobRef.Set_env.empty;
  budget = memo_budget;
  shareable = true;
}

let memo_find m view obj = match view with
  | Public -> GlobRef.Map_env.find_opt obj m.public_closure
  | Implementation -> GlobRef.Map_env.find_opt obj m.implementation_closure

let memo_add m view obj v = match view with
  | Public -> m.public_closure <- GlobRef.Map_env.add obj v m.public_closure
  | Implementation -> m.implementation_closure <- GlobRef.Map_env.add obj v m.implementation_closure

let pending_mem m view obj = match view with
  | Public -> GlobRef.Set_env.mem obj m.pending_public
  | Implementation -> GlobRef.Set_env.mem obj m.pending_implementation

let pending_set m view obj on = match view, on with
  | Public, true -> m.pending_public <- GlobRef.Set_env.add obj m.pending_public
  | Public, false -> m.pending_public <- GlobRef.Set_env.remove obj m.pending_public
  | Implementation, true ->
    m.pending_implementation <- GlobRef.Set_env.add obj m.pending_implementation
  | Implementation, false ->
    m.pending_implementation <- GlobRef.Set_env.remove obj m.pending_implementation

let same_object (view1, obj1) (view2, obj2) =
  (match view1, view2 with
   | Public, Public | Implementation, Implementation -> true
   | Public, Implementation | Implementation, Public -> false)
  && GlobRef.UserOrd.equal obj1 obj2

type step = Enter of vref | Leave of vref

(* [closure_per_root] visits the references of a node with
   [List.rev_append refs todo], so the last reference comes first. The shared
   walk pushes them in the same order, and the [Leave] marker it puts under
   them changes no [Enter]. *)
let push_refs self refs stack =
  List.fold_left (fun stack r -> if same_object r self then stack else Enter r :: stack) stack refs

let shared_closure st m root =
  let rec run = function
    | [] -> ()
    | Enter (view, obj) :: rest ->
      (match memo_find m view obj with
       | Some _ -> run rest
       | None ->
      if pending_mem m view obj then raise Not_shareable
      else begin
        let n = node st view obj in
        incr walk_visits;
        if n.axiom || n.resolved || not (List.is_empty n.flags) then begin
          (* The per-root walk must be the one that reports it. *)
          if not (printable_name st.env obj) then raise Not_shareable
        end;
        pending_set m view obj true;
        run (push_refs (view, obj) n.refs (Leave (view, obj) :: rest))
      end)
    | Leave (view, obj) :: rest ->
      let n = node st view obj in
      let self = (view, obj) in
      let acc =
        List.fold_left (fun acc r ->
            if same_object r self then acc
            else
              let (rview, robj) = r in
              match memo_find m rview robj with
              | Some c -> union_sets acc c
              | None -> raise Not_shareable)
          (node_sets st n obj) n.refs
      in
      m.budget <- m.budget - sets_size acc;
      if m.budget < 0 then raise Not_shareable;
      pending_set m view obj false;
      memo_add m view obj acc;
      run rest
  in
  run [Enter (Public, root)];
  match memo_find m Public root with
  | Some v -> v
  | None -> raise Not_shareable

(** The axioms and flags of every object reachable from [root]. *)
let closure st m root =
  if not m.shareable then closure_per_root st root
  else
    match shared_closure st m root with
    | v -> v
    | exception Not_shareable ->
      m.shareable <- false;
      m.public_closure <- GlobRef.Map_env.empty;
      m.implementation_closure <- GlobRef.Map_env.empty;
      m.pending_public <- GlobRef.Set_env.empty;
      m.pending_implementation <- GlobRef.Set_env.empty;
      closure_per_root st root

(** {6 The type match} *)

(* The universe comparison that checking [Definition f := model] against a
   monomorphic [Parameter f : <type>] of a sealing module type makes (the
   inference mode of kernel/subtyping.ml's [check_constant]): a comparison that
   does not hold yet adds the constraints it needs, if they are consistent with
   the environment. The state is the universe graph with those constraints; the
   error marks a needed constraint that is inconsistent. *)
let infer_universes : (UGraph.t, unit) Conversion.universe_compare =
  let merge csts g =
    match UGraph.merge_constraints csts g with
    | g -> Result.Ok g
    | exception UGraph.UniverseInconsistency _ -> Result.Error (Some ())
  in
  let leq u v g =
    match UGraph.enforce_leq_alg u v g with
    | _, g -> Result.Ok g
    | exception UGraph.UniverseInconsistency _ -> Result.Error (Some ())
  in
  let compare_sorts pb s1 s2 g =
    let holds = match pb with
      | Conversion.CUMUL -> UGraph.check_leq_sort Sorts.Quality.equal g s1 s2
      | Conversion.CONV -> UGraph.check_eq_sort Sorts.Quality.equal g s1 s2
    in
    if holds then Result.Ok g
    (* As pretyping/reductionops.ml's [Infer]: the qualities must already
       compare, and only the universe constraint is inferred. The checked
       comparison above has decided every case with an impredicative sort. *)
    else match s1, s2 with
      | (Sorts.SProp | Sorts.Prop), _ | _, (Sorts.SProp | Sorts.Prop) -> Result.Error None
      | _ when not (Sorts.Quality.equal (Sorts.quality s1) (Sorts.quality s2)) -> Result.Error None
      | _ ->
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        match pb with
        | Conversion.CUMUL -> leq u1 u2 g
        | Conversion.CONV ->
          (* As engine/univSubst.ml's [enforce_eq]: only two levels can be made equal. *)
          match Univ.Universe.level u1, Univ.Universe.level u2 with
          | Some _, Some _ -> Result.bind (leq u1 u2 g) (leq u2 u1)
          | _ -> Result.Error (Some ())
  in
  let compare_instances ~flex u1 u2 g =
    if UGraph.check_eq_instances Sorts.Quality.equal g u1 u2 then Result.Ok g
    else if flex then Result.Error None
    else
      let qcsts, ucsts = UVars.enforce_eq_instances u1 u2 UVars.empty_unif_constraints in
      if UVars.QUnifConstraints.is_trivial qcsts then merge ucsts g else Result.Error None
  in
  let compare_cumul_instances pb variances u1 u2 g =
    let qcsts, ucsts = Conversion.get_cumulativity_constraints pb variances u1 u2 in
    if UVars.QUnifConstraints.is_trivial qcsts then merge ucsts g else Result.Error None
  in
  { Conversion.compare_sorts; compare_instances; compare_cumul_instances }

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
   [universes-differ] for such a model, which the sealing may still accept. *)
let type_verdict env cm trusted =
  let ct = Environ.lookup_constant trusted env in
  let infer env =
    let state = Environ.universes env, infer_universes in
    match Conversion.generic_conv Conversion.CUMUL ~l2r:false TransparentState.full env state
            cm.const_type ct.const_type with
    | Result.Ok _ -> "match"
    | Result.Error None -> "mismatch"
    | Result.Error (Some ()) -> "universes-differ"
  in
  (* The definition's context [am] must be T's context [at]; the types are
     compared under [at]. A failure that ignoring universe levels removes needs a
     constraint that [at] does not give. *)
  let against_polymorphic am at =
    if Subtyping.check_polymorphic_universes env at am then
      let env = Environ.push_context ~strict:false (UVars.AbstractContext.repr at) env in
      match Conversion.default_conv_leq env cm.const_type ct.const_type with
      | Result.Ok () -> "match"
      | Result.Error () ->
        match Conversion.default_conv_leq (Environ.set_type_in_type true env)
                cm.const_type ct.const_type with
        | Result.Ok () -> "universes-differ"
        | Result.Error () -> "mismatch"
    else "universes-differ"
  in
  let minimizable am =
    fst (UVars.AbstractContext.size am) > 0
    || not (PConstraints.is_empty (UVars.UContext.constraints (UVars.AbstractContext.repr am)))
  in
  match cm.const_universes, ct.const_universes with
  | Monomorphic, Monomorphic -> infer env
  | Monomorphic, Polymorphic at -> against_polymorphic UVars.AbstractContext.empty at
  | Polymorphic am, _ when minimizable am -> "universes-differ"
  | Polymorphic am, Monomorphic ->
    (* The model's bound universes are fresh in [env]: they are its instance. The
       definition declares them as global universes, which [Global.push_context_set]
       does with [~strict:true], so each is above [Set] and cannot be taken as it. *)
    infer (Environ.push_context ~strict:true (UVars.AbstractContext.repr am) env)
  | Polymorphic am, Polymorphic at -> against_polymorphic am at

(** {6 The report} *)

(* One message per line, so that a long report never builds one [Pp.t]. *)
let line fmt = Printf.ksprintf (fun s -> Feedback.msg_notice (Pp.str s)) fmt

(* Test-only seam: with the test variable set, print how many objects the
   report's walks entered, so a test can tell one shared walk from one walk
   per request. It has no effect unless the test variable is explicitly set. *)
let test_walk_count () =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_WALK" with
  | Some "1" -> line "walk %d" !walk_visits
  | None | Some _ -> ()

(* Test-only seam: a test sets this for one process to exercise the public
   incomplete-report contract. It has no effect unless the test variable is
   explicitly set. *)
let test_fault () =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_FAILURE" with
  | Some "1" -> CErrors.user_err Pp.(str "test statement-report failure")
  | None | Some _ -> ()

(* The report's format. 2: an [axiom] line also names the axiom's canonical
   kernel name. The first format had no number. *)
let format_version = 2

(* A request's subject that the final environment does not hold, looked up
   in the implementations, as [Print Assumptions] finds a constant that a seal
   hides: each way of splitting the dotted name into a library, modules and a
   label that names a constant field of that module's implementation. Every
   match is returned, so that a name two constants answer to is told apart.
   This only finds which constant a name denotes; the closure printed for it
   is the ordinary one. *)
let resolve_in_impl st name =
  let parts = String.split_on_char '.' name in
  let ids = try Some (List.map Id.of_string parts) with e when CErrors.noncritical e -> None in
  match ids with
  | None -> []
  | Some ids ->
    let n = List.length ids in
    let rec split i acc =
      if i >= n - 1 then acc
      else
        let dir = List.filteri (fun j _ -> j <= i) ids in
        let rest = List.filteri (fun j _ -> j > i) ids in
        let mp0 = ModPath.MPfile (DirPath.make (List.rev dir)) in
        let acc =
          if not (try ignore (Environ.lookup_module mp0 st.env); true with Not_found -> false) then acc
          else
            let rec descend mp = function
              | [lab] ->
                let kn = KerName.make mp (Label.of_id lab) in
                (match in_impl st find_constant kn with
                 | Some _ -> Some (Constant.make1 kn)
                 | None -> None
                 | exception Not_found -> None)
              | m :: rest -> descend (ModPath.MPdot (mp, Label.of_id m)) rest
              | [] -> None
            in
            match descend mp0 rest with
            | Some c when not (List.exists (Constant.UserOrd.equal c) acc) -> c :: acc
            | _ -> acc
        in
        split (i + 1) acc
    in
    List.rev (split 0 [])

let print env access requests =
  let index =
    (* Every constant under each printed name: two kernel names can print
       alike (a library P.A with a module B, and a library P.A.B), and a
       request for such a name answers ambiguous rather than either one. *)
    Environ.fold_constants (fun c _ acc ->
        CString.Map.update (Constant.to_string c)
          (function None -> Some [c] | Some l -> Some (c :: l)) acc)
      env CString.Map.empty
  in
  let st = {
    env; access; fields = ModPath.Map.empty;
    public_nodes = GlobRef.Map_env.empty; implementation_nodes = GlobRef.Map_env.empty; gen = 0;
    keys = Array.make cache_size Constr.mkProp; gens = Array.make cache_size (-1);
  } in
  (* One memo for the whole report: the requests share the walk (see
     "One walk for every request"). *)
  let memo = new_memo () in
  walk_visits := 0;
  line "STATEMENT REPORT %d" format_version;
  test_fault ();

  List.iter (fun r ->
      let trusted = Option.default "-" r.req_trusted in
      let model = match CString.Map.find_opt r.req_model index with
        | Some [c] -> `One c
        | Some _ -> `Ambiguous
        | None ->
          match resolve_in_impl st r.req_model with
          | [] -> `Missing
          (* A type verdict is about the two constants as the final
             environment holds them; one only an implementation holds has
             none there (its type may name the implementation's own
             definitions), so a typed request on it answers as before the
             implementation lookup existed. *)
          | [_] when Option.has_some r.req_trusted -> `Missing
          | [c] -> `One c
          | _ :: _ :: _ -> `Ambiguous
      in
      match model with
      | `Missing -> line "statement %s %s %s model-missing 0 0" r.req_name r.req_model trusted
      | `Ambiguous -> line "statement %s %s %s ambiguous 0 0" r.req_name r.req_model trusted
      | `One model ->
        let c = closure st memo (GlobRef.ConstRef model) in
        let verdict = match r.req_trusted with
          | None -> "not-requested"
          | Some t ->
            match CString.Map.find_opt t index with
            | None -> "trusted-missing"
            | Some [t] -> type_verdict env (Environ.lookup_constant model env) t
            | Some _ -> "trusted-ambiguous"
        in
        line "statement %s %s %s %s %d %d" r.req_name r.req_model trusted verdict
          (CString.Set.cardinal c.axioms) (FlagSet.cardinal c.flag_set);
        CString.Set.iter (line "axiom %s %s" r.req_name) c.axioms;
        (* before the flags: a reader takes resolved lines after the axioms *)
        CString.Set.iter (line "resolved %s %s" r.req_name) c.resolved_fields;
        FlagSet.iter (fun (kind, obj) -> line "flag %s %s %s" r.req_name kind obj) c.flag_set)
    requests;
  test_walk_count ();
  line "END STATEMENT REPORT"
