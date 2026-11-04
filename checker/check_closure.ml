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
(* The processes that read opaque bodies ahead of the walk ("Opaque bodies
   read ahead"). *)
type 'node read_ahead = {
  session : (int * 'node) list CheckWorkers.Forked.t;
  ahead_opaque : Constant.t array;  (* the constants handed out, by position *)
  mutable ticks : int;  (* nodes looked up since the processes were started *)
  mutable last_poll : float;
  mutable finished : bool;  (* no more nodes can come from the processes *)
  gc_start : Gc.stat;
}

type state = {
  env : Environ.env;
  access : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm;
  mutable fields : field_index ModPath.Map.t;
  (* the indexed fields of the implementation of each module looked up so far *)
  mutable public_nodes : node GlobRef.Map_env.t;
  mutable implementation_nodes : node GlobRef.Map_env.t;
  (* each object reached so far, keyed by its constant or by the first
     inductive of its block, in the declaration view that typed its use *)
  mutable prefetched : node Cmap_env.t;
  (* the nodes of [(Public, ConstRef kn)] that forked processes computed
     ahead of the walk ("Opaque bodies read ahead") *)
  mutable cached : Cset_env.t;
  (* the subset of [prefetched] read from a report-node file *)
  mutable ahead : node read_ahead option;
  (* those processes, while they run *)
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
  flags : string list;
  (* the kinds of relaxed typing condition the selected object relies on *)
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

(* A node's flags are the kinds alone; [node_sets] names each by the
   object's path and canonical, as an [axiom] line is, so that two objects
   printing one path keep two flag lines. *)
let typing_flags (tf : typing_flags) acc =
  let add ok kind acc = if ok then acc else kind :: acc in
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

(* What the main process does with an opaque body it cannot read: an opaque
   body that cannot be read is reported as an axiom, as vernac/assumptions.ml's
   [get_constant_body] does: a constant whose body this process cannot see
   rests on something it cannot check. The read can fail for two unrelated
   reasons, though — the proof was not stored, which is what upstream means, or
   the table could not be READ (damaged bytes, or a lazy reader refusing a
   table whose bytes changed since intern) — and the verdict alone does not
   tell them apart. So the failure is named here. The exit status is
   deliberately unchanged: a stored-nowhere body is an ordinary answer, and
   failing the whole check on it would turn every delayed proof into a failed
   grade. A reader who needs certainty reads the warning, which names the
   constant. *)
let warn_unreadable kn e =
  Feedback.msg_warning
    Pp.(str "Statement report: the opaque body of " ++ str (Constant.to_string kn)
        ++ str " could not be read, so it is reported as an axiom: " ++ CErrors.print e)

(* [unreadable] is called on an opaque body that cannot be read; when it
   returns, the constant is an axiom. *)
let constant_node ~unreadable st view kn =
  match lookup_constant st view kn with
  | None -> unresolved
  | Some (declaration_view, cb) ->
    let body, axiom = match cb.const_body with
      | Def c -> [declaration_view, c], false
      | OpaqueDef o ->
        (match (test_unreadable_opaque kn; st.access o) with
         | c, _ -> [declaration_view, c], false
         | exception e when CErrors.noncritical e -> unreadable kn e; [], true)
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
      flags = typing_flags cb.const_typing_flags [] }

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
    let tf = mib.mind_typing_flags in
    let flags = typing_flags tf [] in
    let add cond kind flags = if cond then kind :: flags else flags in
    let flags =
      flags
      |> add (not tf.check_positive) "assumed-positive"
      |> add (uses_uip mib) "uip"
      |> add (not tf.indices_matter
              && Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) mib.mind_packets)
        "indices-not-mattering"
    in
    { refs = refs_to_list refs; axiom = false; flags; resolved = false }

(** {6 Opaque bodies read ahead}

    Reading the opaque bodies and walking them is most of what the report
    costs, and the walk of [closure] does it one constant after another. With
    [-j n], [n - 1] forked processes compute, while the walk goes on, the node
    of [(Public, ConstRef kn)] for the opaque constants [kn] of the
    environment, a chunk of constants at a time to whichever process is free,
    and the walk takes such a node when it has come instead of computing it.
    The main process keeps a core for the walk, looks at the processes every
    few milliseconds ([read_ahead_tick]), and kills them when the walk ends.
    So the report waits for none of them: at worst the walk computes every
    node itself, as without processes.

    The chunks follow the order of the environment, grouped by the library
    whose table holds the bodies. Ordering them by what the walk is likely to
    need first was measured and gained nothing.

    The node a process sends is the one the walk would compute. For a constant
    that the environment holds with a body, [lookup_constant] answers
    [(Public, cb)] with the environment's own declaration and looks at no
    module implementation, so [constant_node] depends only on the environment
    and the opaque accessor, which a forked process has as they are. Its walk
    gives the same set of references whatever the state of [seen], which never
    finds a term of an earlier walk. A process is forked from the main process
    at any point of the walk, whose caches ([public_nodes], [seen], [fields],
    [prefetched]) have grown by then, but none of them changes such a node, so
    the node does not depend on when its process was forked.

    In this case [resolved] is false, and [flags] holds only condition kinds.
    Canonical names, including the [?] token for implementation-only objects,
    are formed later by [node_sets] in the main process. There is no numbering:
    each token is a function of the environment key or the reference's own
    canonical name, whose representative the declaration walk preserves.

    A process sends no node for a body it cannot read, nor for a constant whose
    node raised: the walk computes those itself, so the warning about a body
    that cannot be read is printed where it is printed without processes. A
    process that fails sends no more nodes, and the walk computes the rest.
    Nothing a process does reaches the output ([CheckWorkers.Forked]). *)

exception Unreadable

(* A chunk, what a process is handed at a time, is the opaque constants of
   one library, so that a process reads the table of opaque proofs of a
   library once: at most [read_ahead_chunk_max] of them, and libraries with
   fewer than [read_ahead_chunk_min] go together. *)
let read_ahead_chunk_min = 32
let read_ahead_chunk_max = 128

(* Bytes a process may allocate in its major heap before a fresh one replaces
   it. A process shares the heap of the main process, about the size of the
   environment, until it writes to it. What it adds on top is what it
   allocated in its major heap, plus the inherited pages that the major GC
   slices paid for by that allocation write to, about as much again: at a
   budget of 1 GiB, 16 processes added about 2.25 GB each. So the memory of
   [n] processes beyond the main process grows with [n] times the budget,
   whatever the size of the tree. ROCQCHK_READ_AHEAD_HEAP_BUDGET (in bytes)
   overrides it, to measure another value. *)
let read_ahead_heap_budget () =
  match Option.bind (Sys.getenv_opt "ROCQCHK_READ_AHEAD_HEAP_BUDGET") int_of_string_opt with
  | Some b when b > 0 -> b
  | Some _ | None -> 1 lsl 28

(* Seconds a process has to answer one chunk before it is killed and the
   walk computes its nodes itself. A chunk of a large development takes
   about a second at most (about 6 ms a body, at most 128 bodies), so this
   only stops a process that will not end, for instance on a malformed
   stored proof that no request reaches. *)
let read_ahead_item_timeout = 120.

(* Seconds between two looks at the processes: often enough that a free
   process waits little for its next chunk, rarely enough that looking costs
   nothing next to the walk. *)
let read_ahead_poll_interval = 0.002

(* The opaque constants of the environment, grouped by the library of the
   table that holds their bodies (so a process reads each table once), each
   with that library. *)
let read_ahead_order st =
  let entries =
    Environ.fold_constants (fun kn cb acc -> match cb.const_body with
        | OpaqueDef o when not (Cmap_env.mem kn st.prefetched) ->
          let _, _, dp, _ = Opaqueproof.repr o in (kn, dp) :: acc
        | OpaqueDef _ -> acc
        | Def _ | Undef _ | Primitive _ | Symbol _ -> acc)
      st.env []
  in
  let entries = Array.of_list (List.rev entries) in
  Array.stable_sort (fun (_, a) (_, b) -> DirPath.compare a b) entries;
  entries

(* Where each chunk starts in [libs], the library of each constant, and,
   last, the number of constants. *)
let read_ahead_chunks libs =
  let total = Array.length libs in
  let starts = ref [0] and start = ref 0 in
  for j = 1 to total - 1 do
    let size = j - !start in
    if size >= read_ahead_chunk_max
    || (size >= read_ahead_chunk_min && not (DirPath.equal libs.(j) libs.(j - 1)))
    then begin
      starts := j :: !starts;
      start := j
    end
  done;
  if Int.equal total 0 then [| 0 |] else Array.of_list (List.rev (total :: !starts))

(* Test-only seam, beside [test_fault] below: how many nodes the walk took
   from the processes of [start_read_ahead].
   [COQ_TEST_SUITE_STATEMENT_REPORT_READ_AHEAD] prints it. *)
let read_ahead_used = ref 0
let cached_nodes_used = ref 0

let start_read_ahead st n =
  let ordered = read_ahead_order st in
  let opaque = Array.map fst ordered in
  let bounds = read_ahead_chunks (Array.map snd ordered) in
  (* The nodes of chunk [c], each with its position in [opaque], so that no
     name is sent back. *)
  let chunk c =
    let first = bounds.(c) in
    let rec go j acc =
      if j < first then acc
      else
        let acc =
          match constant_node ~unreadable:(fun _ _ -> raise Unreadable) st Public opaque.(j) with
          | n -> (j, n) :: acc
          | exception _ -> acc
        in
        go (j - 1) acc
    in
    go (bounds.(c + 1) - 1) []
  in
  let gc_start = Gc.quick_stat () in
  let last_poll = Unix.gettimeofday () in
  (* With [lazy_gc], while the processes share the heap of this one, it
     collects as lazily as they do ([CheckWorkers.Forked]). *)
  let session = CheckWorkers.Forked.start ~lazy_gc:true ~heap_budget:(read_ahead_heap_budget ())
      ~item_timeout:read_ahead_item_timeout n chunk (Array.length bounds - 1)
  in
  (* [st.ahead] owns the processes from here: [stop_read_ahead] stops them. *)
  match st.ahead <- Some { session; ahead_opaque = opaque; ticks = 0; last_poll;
                           finished = false; gc_start } with
  | () -> ()
  | exception e -> CheckWorkers.Forked.stop session; raise e

let stop_read_ahead st = match st.ahead with
  | None -> ()
  | Some a ->
    let extra () =
      let s = Gc.quick_stat () in
      Pp.(str "; the walk took " ++ int !read_ahead_used ++ str " nodes, and ran " ++
          int (s.Gc.minor_collections - a.gc_start.Gc.minor_collections) ++
          str " minor and " ++ int (s.Gc.major_collections - a.gc_start.Gc.major_collections) ++
          str " major collections, its heap " ++ int (s.Gc.heap_words / 131072) ++ str " MiB")
    in
    CheckWorkers.Forked.stop ~extra a.session;
    (* Only once its processes have been stopped and waited for, so a stop
       that was interrupted is done again. *)
    st.ahead <- None

(* Takes the nodes that have come, and answers whether more may come. A
   failure only stops the processes: the walk computes the rest. *)
let poll_read_ahead ?wait st a =
  a.last_poll <- Unix.gettimeofday ();
  let deliver _ nodes =
    List.iter (fun (j, n) -> st.prefetched <- Cmap_env.add a.ahead_opaque.(j) n st.prefetched)
      nodes
  in
  match CheckWorkers.Forked.poll ?wait a.session deliver with
  | true -> true
  | false -> a.finished <- true; false
  | exception e when CErrors.noncritical e -> stop_read_ahead st; false

(* Called for each node the walk computes or takes: at a miss on an opaque
   constant, and every 64 nodes, it looks at the processes, at most once every
   [read_ahead_poll_interval], until no more nodes can come from them. *)
let read_ahead_tick st ~miss = match st.ahead with
  | None -> ()
  | Some a when a.finished -> ()
  | Some a ->
    a.ticks <- a.ticks + 1;
    if (miss || Int.equal (a.ticks land 63) 0)
    && Unix.gettimeofday () -. a.last_poll >= read_ahead_poll_interval
    then ignore (poll_read_ahead st a)

let read_ahead_node st view kn =
  let n = match view, st.ahead with
    | Implementation, _ -> read_ahead_tick st ~miss:false; None
    | Public, None -> Cmap_env.find_opt kn st.prefetched
    | Public, Some _ ->
      match Cmap_env.find_opt kn st.prefetched with
      | Some _ as n -> read_ahead_tick st ~miss:false; n
      | None ->
        let opaque = match Environ.lookup_constant_opt kn st.env with
          | Some { const_body = OpaqueDef _; _ } -> true
          | Some _ | None -> false
        in
        read_ahead_tick st ~miss:opaque;
        if opaque then Cmap_env.find_opt kn st.prefetched else None
  in
  if Option.has_some n then
    if Cset_env.mem kn st.cached then incr cached_nodes_used else incr read_ahead_used;
  n

let node st view obj =
  let nodes = match view with
    | Public -> st.public_nodes
    | Implementation -> st.implementation_nodes
  in
  match GlobRef.Map_env.find_opt obj nodes with
  | Some n -> n
  | None ->
    let n = match obj with
      | GlobRef.ConstRef kn ->
        (match read_ahead_node st view kn with
         | Some n -> n
         | None -> constant_node ~unreadable:warn_unreadable st view kn)
      | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
        read_ahead_tick st ~miss:false;
        mind_node st view mind
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
   the key it is stored under there ([Environ.lookup_constant_key]); an object
   that only an implementation holds prints [?] and the term's own name
   instead (see [canonical_token]).
   Two paths to one constant give one canonical name.

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
    | ModPath.MPdot (mp, l) -> root (Id.to_string l :: acc) mp
  in
  let mp, l = KerName.repr kn in
  let r, mods = root [] mp in
  r ^ ":" ^ String.concat "." (mods @ [Id.to_string l])

(* The canonical token printed for [obj], with the kernel name it prints,
   which the name check reads ([printable_name]): one function, so the name
   checked is the name printed. For an object the final environment holds,
   the canonical half of the key it is stored under there. For one only an
   implementation holds, the term's own canonical half after a [?], which a
   reader never joins on: nothing ties that half to a declaration, and the
   name after the [?] keeps two such objects apart (a bare [?] would give two
   distinct axioms of one printed path one entry of the closure's set, and
   the report would list one of them). *)
let canonical_token env obj =
  let known kn = canonical_kername kn, Some kn in
  let unknown kn = "?" ^ canonical_kername kn, Some kn in
  match obj with
  | GlobRef.ConstRef kn ->
    if Environ.mem_constant kn env then
      let _, _, can = Environ.lookup_constant_key kn env in known can
    else unknown (Constant.canonical kn)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    if Environ.mem_mind mind env then
      let _, _, can = Environ.lookup_mind_key mind env in known can
    else unknown (MutInd.canonical mind)
  | GlobRef.VarRef _ -> "-", None

let canonical_of st obj = fst (canonical_token st.env obj)

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
  flag_set =
    (if List.is_empty n.flags then FlagSet.empty
     else
       let entry = axiom_entry st obj in
       List.fold_left (fun s kind -> FlagSet.add (kind, entry) s) FlagSet.empty n.flags);
}

(* Place 2 of the name check (checkNames.mli), for a name that the check at
   load cannot see: a constant or an inductive that a term of an admitted
   library names and that no library declares, which the report prints as an
   axiom. Each object whose name an [axiom] or [flag] line would print is
   tested when the closure reaches it, as are the type names of each inductive
   block it resolves ([mind_node]). This is before the type verdict, whose
   conversion can reach an anomaly that prints an unresolved inductive's name,
   and before the statement's line, so a refusal leaves no END STATEMENT
   REPORT line.

   The name of [obj] the report must not print, if there is one: the user
   half when it is not made of identifiers, else the canonical half printed
   ([canonical_token]) when that one is not, so a refusal quotes the text that
   failed. *)
let unprintable_name env obj =
  let user_ok = match obj with
    | GlobRef.ConstRef kn -> CheckNames.valid_kername (Constant.user kn)
    | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
      CheckNames.valid_kername (MutInd.user mind)
    | GlobRef.VarRef id -> CheckNames.valid_id id
  in
  if not user_ok then Some (name_of obj)
  else match snd (canonical_token env obj) with
    | Some kn when not (CheckNames.valid_kername kn) -> Some (canonical_kername kn)
    | Some _ | None -> None

let printable_name env obj = match unprintable_name env obj with None -> true | Some _ -> false

(** {6 Report nodes saved by a previous check}

    Only public opaque nodes are reusable. The caller supplies whole-file
    SHA256 digests, not Rocq's load digests, which do not cover opaque bodies.
    It also supplies the libraries this invocation actually checked: those
    must never take a saved node, even if the admission list names them.
    A file is trusted evidence only when its transport is trusted; the header
    identifies this encoding and checker build, not the file's provenance. *)

let new_state env access = {
  env; access; fields = ModPath.Map.empty;
  public_nodes = GlobRef.Map_env.empty; implementation_nodes = GlobRef.Map_env.empty;
  prefetched = Cmap_env.empty; cached = Cset_env.empty; ahead = None; gen = 0;
  keys = Array.make cache_size Constr.mkProp; gens = Array.make cache_size (-1);
}

let rec library_of_modpath = function
  | ModPath.MPfile dp -> Some dp
  | ModPath.MPdot (mp, _) -> library_of_modpath mp
  | ModPath.MPbound _ -> None

let library_of_constant kn = library_of_modpath (Constant.modpath kn)

let opaque_owned_by dp o =
  let _, _, owner, _ = Opaqueproof.repr o in
  DirPath.equal dp owner

let valid_sha256 s =
  String.length s = 64 && String.for_all (function
      | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
      | _ -> false) s

let report_nodes_max_bytes = 4_294_967_296L
let report_list_max_bytes = 67_108_864L
let report_list_max_line = 65_536

let open_regular_input ~max_bytes file =
  let check (info : Unix.LargeFile.stats) =
    if info.st_kind <> Unix.S_REG || info.st_size < 0L || info.st_size > max_bytes then raise Exit
  in
  check (Unix.LargeFile.stat file);
  (* Nonblocking open and a second check also close the stat/open FIFO race. *)
  let fd = Unix.openfile file [Unix.O_RDONLY; Unix.O_NONBLOCK] 0 in
  try
    let info = Unix.LargeFile.fstat fd in
    check info;
    let ch = Unix.in_channel_of_descr fd in
    set_binary_mode_in ch true;
    ch, info.st_size
  with e -> Unix.close fd; raise e

let bounded_line ch limit =
  let b = Buffer.create (min limit 80) in
  let rec loop () = match input_char ch with
    | '\n' -> Buffer.contents b
    | c ->
      if Buffer.length b >= limit then raise Exit;
      Buffer.add_char b c; loop ()
    | exception End_of_file ->
      if Buffer.length b = 0 then raise End_of_file else Buffer.contents b
  in
  loop ()

(* A malformed list is ignored as a whole, including duplicate libraries.
   Parse identifiers without [Id.of_string]'s warning/error path. *)
let read_node_digests file =
  let ch, file_size = open_regular_input ~max_bytes:report_list_max_bytes file in
  Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
      let rec loop acc = match bounded_line ch report_list_max_line with
        | exception End_of_file -> acc
        | line ->
          if LargeFile.pos_in ch > file_size then raise Exit;
          match String.split_on_char ' ' line with
          | [name; sha] when valid_sha256 sha ->
            let ids = String.split_on_char '.' name in
            if not (List.for_all Id.is_valid ids) then raise Exit;
            let dp = DirPath.make (List.rev_map Id.of_string ids) in
            if DirPath.Map.mem dp acc then raise Exit;
            loop (DirPath.Map.add dp (String.lowercase_ascii sha) acc)
          | _ -> raise Exit
      in
      loop DirPath.Map.empty)

let report_nodes_header () =
  ["ROCQCHK REPORT NODES 1"; Coq_config.version;
   Digest.to_hex (Digest.file Sys.executable_name)]

type saved_node_group = DirPath.t * string * (Constant.t * node) list

(* Reject cycles before typed decoding, so a malformed list or module path
   cannot loop. No native block is reconstructed from this reification. *)
let check_acyclic (root, memory) =
  let open Analyze in
  let seen = LargeArray.make (LargeArray.length memory) 0 in
  let push data rest = match data with Ptr p -> (p, false) :: rest | _ -> rest in
  let rec loop = function
    | [] -> ()
    | (p, true) :: rest -> LargeArray.set seen p 2; loop rest
    | (p, false) :: rest ->
      match LargeArray.get seen p with
      | 1 -> raise Exit
      | 2 -> loop rest
      | _ ->
        LargeArray.set seen p 1;
        let rest = (p, true) :: rest in
        let rest = match LargeArray.get memory p with
          | Struct (_, fields) ->
            let pending = ref rest in
            for i = Array.length fields - 1 downto 0 do
              pending := push fields.(i) !pending
            done;
            !pending
          | String _ | Int64 _ | Float64 _ -> rest
        in
        loop rest
  in
  loop (push root [])

(* Bound module identifiers cannot be recreated with [MBId.make], which
   allocates a fresh identity. Recover the existing typed identity from its
   library's module declarations instead. *)
let existing_mbid env uid id dp =
  let exception Found of MBId.t in
  let check mbid =
    let n, name, lib = MBId.repr mbid in
    if n = uid && Id.equal name id && DirPath.equal lib dp then raise (Found mbid)
  in
  let rec signature depth = function
    | _ when depth > 1024 -> raise Exit
    | MoreFunctor (mbid, mtb, tail) ->
      check mbid; signature (depth + 1) (mod_type mtb); signature (depth + 1) tail
    | NoFunctor fields -> structure (depth + 1) fields
  and structure depth fields =
    List.iter (fun (_, field) -> match field with
        | SFBmodule mb -> module_body depth mb
        | SFBmodtype mtb -> signature depth (mod_type mtb)
        | SFBconst _ | SFBmind _ | SFBrules _ -> ()) fields
  and module_body depth mb =
    signature depth (mod_type mb);
    match mod_expr mb with
    | Struct (_, fields) -> structure (depth + 1) fields
    | Abstract | Algebraic _ | FullStruct -> ()
  in
  try module_body 0 (Environ.lookup_module (ModPath.MPfile dp) env); raise Exit
  with Found mbid -> mbid

let decode_node_groups env (root, memory) =
  let open Analyze in
  let object_at = function
    | Ptr p -> LargeArray.get memory p
    | Int _ | Atm _ | Fun _ -> raise Exit
  in
  let block tag size data = match object_at data with
    | Struct (actual, fields) when actual = tag && Array.length fields = size -> fields
    | Struct _ | String _ | Int64 _ | Float64 _ -> raise Exit
  in
  let integer = function Int n -> n | Ptr _ | Atm _ | Fun _ -> raise Exit in
  let string data = match object_at data with
    | String s -> s
    | Struct _ | Int64 _ | Float64 _ -> raise Exit
  in
  let boolean = function Int 0 -> false | Int 1 -> true | _ -> raise Exit in
  (* Bound both typed construction and subsequent import work. Memoization
     preserves the wire DAG; this budget is a second line of defence if a
     schema is interpreted in several contexts or a shared list is visited
     repeatedly during admission. Exhaustion rejects only the cache. *)
  let objects = LargeArray.length memory in
  let remaining = ref (if objects >= max_int / 64 then max_int else 64 * (objects + 1)) in
  let charge cells =
    if cells > !remaining then raise Exit;
    remaining := !remaining - cells
  in
  let memo table decode data = match data with
    | Ptr p ->
      (match Hashtbl.find_opt table p with
       | Some value -> value
       | None ->
         charge 1;
         let value = decode data in
         Hashtbl.add table p value; value)
    | Int _ | Atm _ | Fun _ -> decode data
  in
  (* Each schema gets its own typed suffix table. Build only the uncached
     prefix, then attach it to the existing suffix without copying it. *)
  let list decode =
    let suffixes = Hashtbl.create 127 in
    let rec finish pending tail = match pending with
      | [] -> tail
      | (p, value) :: rest ->
        charge 1;
        let values = value :: tail in
        Hashtbl.add suffixes p values;
        finish rest values
    in
    let rec loop pending = function
      | Int 0 -> finish pending []
      | Ptr p as data ->
        (match Hashtbl.find_opt suffixes p with
         | Some values -> finish pending values
         | None ->
           let fields = block 0 2 data in
           let value = decode fields.(0) in
           charge 2;
           loop ((p, value) :: pending) fields.(1))
      | Int _ | Atm _ | Fun _ -> raise Exit
    in
    loop []
  in
  let ids = Hashtbl.create 127 and paths = Hashtbl.create 127 in
  let modules = Hashtbl.create 127 and kernels = Hashtbl.create 127 in
  let constants = Hashtbl.create 127 and minds = Hashtbl.create 127 in
  let mbids = Hashtbl.create 17 and inductives = Hashtbl.create 127 in
  let references = Hashtbl.create 127 and vrefs = Hashtbl.create 127 in
  let nodes = Hashtbl.create 127 and entries = Hashtbl.create 127 in
  let groups = Hashtbl.create 127 in
  let bound = Hashtbl.create 17 in
  let id = memo ids (fun data ->
      let s = string data in
      if not (Id.is_valid s) then raise Exit;
      Id.of_string s) in
  let ids_list = list id in
  let dirpath = memo paths (fun data -> DirPath.make (ids_list data)) in
  let mbid = memo mbids (fun data ->
    let fields = block 0 3 data in
    let uid = integer fields.(0) and name = id fields.(1) and dp = dirpath fields.(2) in
    let key = uid, name, dp in
    match Hashtbl.find_opt bound key with
    | Some mbid -> mbid
    | None -> let mbid = existing_mbid env uid name dp in Hashtbl.add bound key mbid; mbid)
  in
  let rec modpath depth data =
    if depth > 1024 then raise Exit;
    memo modules (fun data -> match object_at data with
        | Struct (0, [|dp|]) -> charge 1; ModPath.MPfile (dirpath dp), 0
        | Struct (1, [|name|]) -> charge 1; ModPath.MPbound (mbid name), 0
        | Struct (2, [|parent; label|]) ->
          let parent, height = modpath (depth + 1) parent in
          if height >= 1024 then raise Exit;
          charge 1;
          ModPath.MPdot (parent, id label), height + 1
        | _ -> raise Exit) data
  in
  let kername = memo kernels (fun data ->
      let fields = block 0 3 data in
      ignore (integer fields.(2));
      let path, _ = modpath 0 fields.(0) in
      KerName.make path (id fields.(1))) in
  let constant = memo constants (fun data -> match object_at data with
      | Struct (0, [|kn|]) -> Constant.make1 (kername kn)
      | Struct (1, [|user; canonical|]) -> Constant.make (kername user) (kername canonical)
      | _ -> raise Exit) in
  let mind = memo minds (fun data -> match object_at data with
      | Struct (0, [|kn|]) -> MutInd.make1 (kername kn)
      | Struct (1, [|user; canonical|]) -> MutInd.make (kername user) (kername canonical)
      | _ -> raise Exit) in
  let inductive = memo inductives (fun data ->
    let fields = block 0 2 data in
    let index = integer fields.(1) in
    if index < 0 then raise Exit;
    mind fields.(0), index)
  in
  let reference = memo references (fun data -> match object_at data with
    | Struct (0, [|name|]) -> GlobRef.VarRef (id name)
    | Struct (1, [|name|]) -> GlobRef.ConstRef (constant name)
    | Struct (2, [|name|]) -> GlobRef.IndRef (inductive name)
    | Struct (3, [|name|]) ->
      let fields = block 0 2 name in
      let index = integer fields.(1) in
      if index <= 0 then raise Exit;
      charge 1;
      GlobRef.ConstructRef (inductive fields.(0), index)
    | _ -> raise Exit)
  in
  let vref = memo vrefs (fun data ->
    let fields = block 0 2 data in
    let view = match fields.(0) with Int 0 -> Public | Int 1 -> Implementation | _ -> raise Exit in
    view, reference fields.(1))
  in
  let refs_list = list vref and flags_list = list string in
  let node = memo nodes (fun data ->
    let fields = block 0 4 data in
    { refs = refs_list fields.(0); axiom = boolean fields.(1);
      flags = flags_list fields.(2); resolved = boolean fields.(3) })
  in
  let entry = memo entries (fun data ->
    let fields = block 0 2 data in
    constant fields.(0), node fields.(1))
  in
  let entry_list = list entry in
  let group = memo groups (fun data ->
    let fields = block 0 3 data in
    dirpath fields.(0), string fields.(1), entry_list fields.(2))
  in
  let group_list = list group in
  let groups : saved_node_group list = group_list root in
  groups, charge


let reusable_node ?(charge = fun _ -> ()) st kn n =
  charge 1;
  not n.axiom && not n.resolved
  && printable_name st.env (GlobRef.ConstRef kn)
  && List.for_all (fun (_, obj) -> charge 1; printable_name st.env obj) n.refs

let read_report_nodes st ~checked (file, admit) =
  try
    if Option.has_some (Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE") then raise Exit;
    let admitted = read_node_digests admit in
    let header = report_nodes_header () in
    let ch, file_size = open_regular_input ~max_bytes:report_nodes_max_bytes file in
    let groups, charge =
      Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
          List.iter (fun expected ->
              if not (String.equal (bounded_line ch report_list_max_line) expected) then raise Exit) header;
          let remaining = Int64.sub file_size (LargeFile.pos_in ch) in
          if remaining <= 0L || remaining > Int64.of_int max_int then raise Exit;
          let data = Analyze.parse_channel ~quiet:true ~length:(Int64.to_int remaining) ch in
          check_acyclic data;
          decode_node_groups st.env data)
    in
    let prefetched, cached, _ =
      List.fold_left (fun (prefetched, cached, seen) (dp, sha, nodes) ->
          charge 1;
          if DirPath.Set.mem dp seen then raise Exit;
          let seen = DirPath.Set.add dp seen in
          let eligible =
            not (DirPath.Set.mem dp checked)
            && match DirPath.Map.find_opt dp admitted with
            | Some expected -> String.equal sha expected
            | None -> false
          in
          if not eligible then prefetched, cached, seen
          else
            let prefetched, cached = List.fold_left (fun (prefetched, cached) (kn, n) ->
                charge 1;
                let belongs = match library_of_constant kn with
                  | Some lib -> DirPath.equal lib dp
                  | None -> false
                in
                match Environ.lookup_constant_opt kn st.env with
                | Some { const_body = OpaqueDef o; _ }
                  when belongs && opaque_owned_by dp o && reusable_node ~charge st kn n ->
                  if Cset_env.mem kn cached then raise Exit;
                  Cmap_env.add kn n prefetched, Cset_env.add kn cached
                | Some _ | None -> prefetched, cached)
              (prefetched, cached) nodes in
            prefetched, cached, seen)
        (st.prefetched, st.cached, DirPath.Set.empty) groups
    in
    (* Commit only after the whole file and every group have been read. *)
    st.prefetched <- prefetched;
    st.cached <- cached
  with e when CErrors.noncritical e -> ()

let write_report_nodes st (file, digests) =
  try
    let digests = read_node_digests digests in
    let header = report_nodes_header () in
    let groups = Environ.fold_constants (fun kn cb groups ->
        match cb.const_body, library_of_constant kn with
        | OpaqueDef o, Some dp when DirPath.Map.mem dp digests && opaque_owned_by dp o ->
          let n = try
              let n = match GlobRef.Map_env.find_opt (GlobRef.ConstRef kn) st.public_nodes with
                | Some n -> n
                | None ->
                  match Cmap_env.find_opt kn st.prefetched with
                  | Some n -> n
                  | None -> constant_node ~unreadable:(fun _ _ -> raise Unreadable) st Public kn
              in
              if reusable_node st kn n then Some n else None
            with e when CErrors.noncritical e -> None
          in
          (match n with
           | None -> groups
           | Some n -> DirPath.Map.update dp
               (function None -> Some [kn, n] | Some nodes -> Some ((kn, n) :: nodes)) groups)
        | _ -> groups)
      st.env DirPath.Map.empty in
    let groups = DirPath.Map.fold (fun dp nodes acc ->
        (dp, DirPath.Map.find dp digests, nodes) :: acc) groups [] in
    let tmp, ch = Filename.open_temp_file ~temp_dir:(Filename.dirname file)
        ~mode:[Open_binary] (Filename.basename file ^ ".") ".tmp" in
    Fun.protect
      ~finally:(fun () ->
          close_out_noerr ch;
          try Sys.remove tmp with e when CErrors.noncritical e -> ())
      (fun () ->
         List.iter (fun s -> output_string ch s; output_char ch '\n') header;
         Marshal.to_channel ch groups [];
         close_out ch;
         Sys.rename tmp file)
  with e when CErrors.noncritical e -> ()

let save_nodes env access ~file ~digests =
  try write_report_nodes (new_state env access) (file, digests)
  with e when CErrors.noncritical e -> ()

let check_printed_name env obj =
  match unprintable_name env obj with
  | None -> ()
  | Some name ->
    CErrors.user_err
      Pp.(str ("The statement report would print the name " ^ CheckNames.quote name ^
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

(* Test-only seam: with the test variable set, print how many nodes the walk
   took from the processes of [start_read_ahead], so a test can tell that they were
   used, and make the walk wait until the processes have answered every chunk,
   so that the count does not depend on how fast they are. It has no effect
   unless the test variable is explicitly set. *)
let test_read_ahead_count () =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_READ_AHEAD" with
  | Some "1" -> line "read ahead %d" !read_ahead_used
  | None | Some _ -> ()

let test_read_ahead_wait st =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_READ_AHEAD", st.ahead with
  | Some "1", Some a -> while poll_read_ahead ~wait:1. st a do () done
  | (None | Some _), _ -> ()

(* Test-only seam: a test sets this for one process to exercise the public
   incomplete-report contract. It has no effect unless the test variable is
   explicitly set. *)
let test_fault () =
  match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_FAILURE" with
  | Some "1" -> CErrors.user_err Pp.(str "test statement-report failure")
  | None | Some _ -> ()

(* The report's format. 2: an [axiom] line also names the axiom's canonical
   kernel name. 3: a [flag] line too, and a canonical only an implementation
   holds is printed after a [?]. The first format had no number. *)
let format_version = 3

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
                let kn = KerName.make mp lab in
                (match in_impl st find_constant kn with
                 | Some _ -> Some (Constant.make1 kn)
                 | None -> None
                 | exception Not_found -> None)
              | m :: rest -> descend (ModPath.MPdot (mp, m)) rest
              | [] -> None
            in
            match descend mp0 rest with
            | Some c when not (List.exists (Constant.UserOrd.equal c) acc) -> c :: acc
            | _ -> acc
        in
        split (i + 1) acc
    in
    List.rev (split 0 [])

let print ~jobs ?nodes_in ?nodes_out ~checked env access requests =
  let index =
    (* Every constant under each printed name: two kernel names can print
       alike (a library P.A with a module B, and a library P.A.B), and a
       request for such a name answers ambiguous rather than either one. *)
    Environ.fold_constants (fun c _ acc ->
        CString.Map.update (Constant.to_string c)
          (function None -> Some [c] | Some l -> Some (c :: l)) acc)
      env CString.Map.empty
  in
  let st = new_state env access in
  Option.iter (read_report_nodes st ~checked) nodes_in;
  (* One memo for the whole report: the requests share the walk (see
     "One walk for every request"). *)
  let memo = new_memo () in
  walk_visits := 0;
  read_ahead_used := 0;
  cached_nodes_used := 0;
  line "STATEMENT REPORT %d" format_version;
  test_fault ();
  (* Read ahead only when some request has a model to walk, with one process
     fewer than [jobs]: this one walks. The walk computes whatever the
     processes did not: a failure here only leaves it more to compute. No
     process outlives the walk, whichever way it ends: the processes are
     stopped in a [finally] that is in place before they start. *)
  Fun.protect ~finally:(fun () -> stop_read_ahead st) (fun () ->
      if jobs > 1 && List.exists (fun r -> CString.Map.mem r.req_model index) requests then
        (try start_read_ahead st (jobs - 1)
         with e when CErrors.noncritical e -> ());
      test_read_ahead_wait st;
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
            FlagSet.iter (fun (kind, entry) -> line "flag %s %s %s" r.req_name kind entry) c.flag_set)
        requests);
  test_walk_count ();
  test_read_ahead_count ();
  (match Sys.getenv_opt "COQ_TEST_SUITE_STATEMENT_REPORT_CACHED_NODES" with
   | Some "1" -> line "cached nodes %d" !cached_nodes_used
   | None | Some _ -> ());
  line "END STATEMENT REPORT";
  Option.iter (write_report_nodes st) nodes_out
