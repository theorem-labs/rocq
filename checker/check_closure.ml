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
        | OpaqueDef o -> let _, _, dp, _ = Opaqueproof.repr o in (kn, dp) :: acc
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
  if Option.has_some n then incr read_ahead_used;
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
   block it resolves ([mind_node]). This is before the type verdict, whose
   conversion can reach an anomaly that prints an unresolved inductive's name,
   and before the statement's line, so a refusal leaves no END STATEMENT
   REPORT line. *)
let printable_name obj =
  match obj with
  | GlobRef.ConstRef kn -> CheckNames.valid_kername (Constant.user kn)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    CheckNames.valid_kername (MutInd.user mind)
  | GlobRef.VarRef id -> CheckNames.valid_id id

let check_printed_name obj =
  if not (printable_name obj) then
    CErrors.user_err
      Pp.(str ("The statement report would print the name " ^ CheckNames.quote (name_of obj) ^
               ", which is not made of identifiers."))

module FlagSet = Stdlib.Set.Make (struct
    type t = string * string
    let compare (k1, o1) (k2, o2) =
      let c = String.compare k1 k2 in
      if Int.equal c 0 then String.compare o1 o2 else c
  end)

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
        incr walk_visits;
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
  mutable public_closure : (CString.Set.t * FlagSet.t) GlobRef.Map_env.t;
  mutable implementation_closure : (CString.Set.t * FlagSet.t) GlobRef.Map_env.t;
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
        if n.axiom || not (List.is_empty n.flags) then begin
          (* The per-root walk must be the one that reports it. *)
          if not (printable_name obj) then raise Not_shareable
        end;
        pending_set m view obj true;
        run (push_refs (view, obj) n.refs (Leave (view, obj) :: rest))
      end)
    | Leave (view, obj) :: rest ->
      let n = node st view obj in
      let axioms = if n.axiom then CString.Set.singleton (name_of obj) else CString.Set.empty in
      let flags = List.fold_left (fun s f -> FlagSet.add f s) FlagSet.empty n.flags in
      let self = (view, obj) in
      let axioms, flags =
        List.fold_left (fun (a, f) r ->
            if same_object r self then (a, f)
            else
              let (rview, robj) = r in
              match memo_find m rview robj with
              | Some (a', f') -> CString.Set.union a a', FlagSet.union f f'
              | None -> raise Not_shareable)
          (axioms, flags) n.refs
      in
      m.budget <- m.budget - CString.Set.cardinal axioms - FlagSet.cardinal flags;
      if m.budget < 0 then raise Not_shareable;
      pending_set m view obj false;
      memo_add m view obj (axioms, flags);
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
let type_verdict env model trusted =
  let cm = Environ.lookup_constant model env and ct = Environ.lookup_constant trusted env in
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

let print ~jobs env access requests =
  let index =
    Environ.fold_constants (fun c _ acc -> CString.Map.add (Constant.to_string c) c acc)
      env CString.Map.empty
  in
  let st = {
    env; access; fields = ModPath.Map.empty;
    public_nodes = GlobRef.Map_env.empty; implementation_nodes = GlobRef.Map_env.empty;
    prefetched = Cmap_env.empty; ahead = None; gen = 0;
    keys = Array.make cache_size Constr.mkProp; gens = Array.make cache_size (-1);
  } in
  (* One memo for the whole report: the requests share the walk (see
     "One walk for every request"). *)
  let memo = new_memo () in
  walk_visits := 0;
  read_ahead_used := 0;
  line "STATEMENT REPORT";
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
          match CString.Map.find_opt r.req_model index with
          | None -> line "statement %s %s %s model-missing 0 0" r.req_name r.req_model trusted
          | Some model ->
            let axioms, flags = closure st memo (GlobRef.ConstRef model) in
            let verdict = match r.req_trusted with
              | None -> "not-requested"
              | Some t ->
                match CString.Map.find_opt t index with
                | None -> "trusted-missing"
                | Some t -> type_verdict env model t
            in
            line "statement %s %s %s %s %d %d" r.req_name r.req_model trusted verdict
              (CString.Set.cardinal axioms) (FlagSet.cardinal flags);
            CString.Set.iter (line "axiom %s %s" r.req_name) axioms;
            FlagSet.iter (fun (kind, obj) -> line "flag %s %s %s" r.req_name kind obj) flags)
        requests);
  test_walk_count ();
  test_read_ahead_count ();
  line "END STATEMENT REPORT"
