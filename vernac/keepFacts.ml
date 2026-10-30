(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(* The facts the keep rule reads beside the library label that cannot be
   recomputed from a [.vo] file's segments alone (design D18,
   dispatch://INFRA-361, Astra review 2 blockers 1 and 3). [Library] computes
   them while a library is saved, when the whole environment is loaded, and
   stores them in a [keepfacts] segment that the label does not cover (so an
   [Admitted -> Qed] edit, which the label hides on purpose, does not move
   through this). The keep rule reads them through [rocq-library-label
   --axiom-report-json]. *)

type query = {
  constant : string;  (** its user name *)
  library : string option;  (** the library holding it; [None] for a functor parameter's *)
  opaque : bool;
  (** for a status check, whether it was an opaque proof when the command ran;
      for a body read, always [true]: an opaque proof whose body was read *)
  table : string option;
  (** for a body read -- by an extraction, or by the walk that computes the
      closures, of a constant of this library -- the library whose opaque
      table holds that body; [None] for a status check (a strategy command,
      an extraction's axiom-or-opaque check) *)
}

type t = {
  assumptions : (string * string list) list option;
  (** The assumption closure of each constant and inductive the library
      declares, by user name: the axioms (and other [ContextObject]s, as sorted
      canonical keys, plus the theory flags the closure needs) the declaration
      transitively relies on, traversing opaque proof bodies the way [Print
      Assumptions] does. Sorted by name; a declaration with an empty closure is
      left out. [None] when it could not be computed (a delegated proof body
      was not available), which the keep rule treats as a reason to rebuild.
      The keep rule's monotone condition requires each declaration's closure
      only to shrink: an opaque proof that starts using an existing axiom grows
      it, with every declaration status and the library label unchanged. It is
      per declaration, not per library, because a library's union always holds
      its own axioms, so a proof of the same library starting to use one would
      not move it. *)
  opacity_queries : query list;
  (** Each foreign constant (its user name) that a command of this library
      told apart as an axiom or an opaque proof -- a non-opaque
      [Strategy]/[Transparent] command, an extraction ([OpacityLog]) -- while
      its body was [Undef None] ([opaque = false]) or an opaque proof
      ([opaque = true]), or whose opaque proof body an extraction read
      ([opaque = true], with [table] the library whose opaque table it read);
      a constant of any other body form is not recorded. A constant of this
      library is recorded too when an extraction, or the walk that computes
      [assumptions] ([logging_access]), read its body from another library's
      table (a copy made here of another library's proof: a functor
      application, an [Include] of one, a sealed module whose implementation
      is such an expression). A constant recorded several ways is
      [opaque = true] if any record is, with the table of its body read
      ([collect_opacity]).
      Sorted by name. The keep rule rebuilds a dependent when the recorded
      opacity no longer matches the dependency's current one -- the command
      could then error, or stop erroring, on a real recompile -- and keeps a
      dependent that read a body only when the holder's object and the
      table's object are both byte-identical. *)
}

(* The [MPfile] root of a module path, [None] for a bound (functor-parameter)
   path. *)
let rec mpfile_root = function
  | ModPath.MPfile dp -> Some dp
  | ModPath.MPdot (mp, _) -> mpfile_root mp
  | ModPath.MPbound _ -> None

let is_self self mp =
  match mpfile_root mp with Some dp -> DirPath.equal dp self | None -> false

(* The references of every constant and inductive this library declares -- the
   roots of its assumption closure. A functor's own (uninstantiated) body
   constants are not in the environment, so they are not roots; an applied
   functor's results are, under the applying module's path. *)
let library_roots self =
  let env = Global.env () in
  let consts =
    Environ.fold_constants
      (fun c _ acc ->
        if is_self self (Constant.modpath c)
        then (Constant.to_string c, GlobRef.ConstRef c) :: acc else acc)
      env [] in
  Environ.fold_inductives
    (fun m _ acc ->
      if is_self self (MutInd.modpath m)
      then (MutInd.to_string m, GlobRef.IndRef (m, 0)) :: acc else acc)
    env consts

let grkey = function
  | GlobRef.ConstRef c -> "c:" ^ KerName.to_string (Constant.canonical c)
  | GlobRef.IndRef (m, i) ->
    "i:" ^ KerName.to_string (MutInd.canonical m) ^ "." ^ string_of_int i
  | GlobRef.ConstructRef ((m, i), j) ->
    "k:" ^ KerName.to_string (MutInd.canonical m) ^ "." ^ string_of_int i
    ^ "." ^ string_of_int j
  | GlobRef.VarRef id -> "v:" ^ Id.to_string id

let axiom_key = function
  | Printer.Constant c -> "axiom:" ^ KerName.to_string (Constant.canonical c)
  | Printer.Positive m -> "positive:" ^ KerName.to_string (MutInd.canonical m)
  | Printer.Guarded gr -> "guarded:" ^ grkey gr
  | Printer.TypeInType gr -> "typeintype:" ^ grkey gr
  | Printer.UncheckedEliminations gr -> "unchecked_elim:" ^ grkey gr
  | Printer.UIP m -> "uip:" ^ KerName.to_string (MutInd.canonical m)
  | Printer.IndicesNotMattering m -> "indices:" ^ KerName.to_string (MutInd.canonical m)

let context_object_key = function
  | Printer.Variable id -> "variable:" ^ Id.to_string id
  | Printer.Axiom (ax, _) -> axiom_key ax
  | Printer.Opaque c -> "opaque:" ^ KerName.to_string (Constant.canonical c)
  | Printer.Transparent c -> "transparent:" ^ KerName.to_string (Constant.canonical c)

(* The keys of what [Assumptions.assumptions] (or [object_assumptions]) gives:
   one per [ContextObject], plus the theory flags. *)
let keys (theory, m) =
  let acc =
    Printer.ContextObjectMap.fold (fun k _ acc -> context_object_key k :: acc) m [] in
  let flag name b acc = if b then ("theory:" ^ name) :: acc else acc in
  let acc = flag "impredicative_set" theory.Printer.has_impredicative_set acc in
  let acc = flag "rewrite_rules" theory.Printer.has_rewrite_rules acc in
  let acc = flag "type_in_type" theory.Printer.has_type_in_type acc in
  flag "unchecked_eliminations" theory.Printer.has_unchecked_eliminations acc

(* The closure of one root by its own [Print Assumptions] query, which walks
   every body it reaches, foreign ones included: the definition the
   computation below must reproduce. *)
let closure_of access st root =
  List.sort_uniq String.compare
    (keys (Assumptions.assumptions ~add_opaque:false ~add_transparent:false access st [root]))

(* ROCQ_KEEPFACTS_FULL_WALK=1 computes every closure by [closure_of], the
   reference the computation below is checked against
   (misc/library-label-keepfacts.sh, and the equality of every closure over a
   whole Stdlib build); ROCQ_KEEPFACTS_DEBUG=1 says on standard error how each
   library's closures were computed. Both are read once, at startup. *)
let full_walk = Sys.getenv_opt "ROCQ_KEEPFACTS_FULL_WALK" = Some "1"
let debug = Sys.getenv_opt "ROCQ_KEEPFACTS_DEBUG" = Some "1"

exception Full_walk of string

module SSet = CString.Set

(* Every root's closure from one walk, which does not enter a foreign object
   whose library stored its closure.

   The closure of an object is the union of what each object reachable from
   it contributes by itself ([Assumptions.object_assumptions]), so it is what
   the object contributes plus the closures of its direct references
   (the walk's graph, [Assumptions.reach]). A foreign object takes the closure
   its library stored when it was compiled ([stored dp], the [keepfacts]
   segment [Library] read with the library's other segments) instead of being
   walked.

   What that stored closure is. It is the closure the walk gave when that
   library was compiled, against its dependencies then. So it equals what a
   walk of the bodies gives now when no library it reaches was recompiled
   since. A library rebuilt to an equal label is loaded by a dependent that
   was compiled against its old build, and the keep rule leaves dependents in
   that state (a keep round): there the stored closure can differ from a walk
   of the current bodies, and the keep rule makes it a superset of it.

   The premise: every kept object is a registration object, and a
   registration never keeps: each library it stages it either compiles, or
   takes from the registration object store as an object an earlier
   registration compiled from identical inputs, against the same
   prerequisite objects. So every record a registration wrote is exact for
   its library's own declarations against the objects it was compiled with.
   The keep rule keeps a library only when no declaration's closure in any
   library of its transitive in-tree closure grew (its monotone condition,
   s1b) AND every table named in its own body-read queries is
   byte-identical: the growth check alone is not enough, since a copy whose
   body sits in another library's table can gain an axiom while that
   library's label and every closure it stores stay the same
   (misc/library-label-keepfacts.sh, BXA).
   Then every closure a kept library recorded still contains the current
   one: by induction over the dependency order, a library's record is its
   own declarations' contributions (exact, by the premise, and unchanged
   while the tables its copies read are byte-identical) plus its
   dependencies' records, each of which contains the dependency's current
   closure; and a kept object is byte-identical, so its record is the one it
   wrote. A closure computed here is then a superset of the full walk's,
   never a subset: it can list an axiom a dependency rebuilt to an equal
   label no longer uses (an [Admitted] lemma since proved), and it never
   misses one the bodies use. The premise is what rules out the other case:
   a record computed by [every_walk] (the fallback, or
   ROCQ_KEEPFACTS_FULL_WALK=1) over a baseline that itself held kept objects
   walks their current bodies rather than taking their stored closures, so
   it could be smaller than the stored-closure walk's, and the superset
   statement above would not hold for it. Outside the keep rule (a hand-made
   mix of stale and rebuilt objects) nothing makes it a superset.
   misc/library-label-keepfacts.sh shows both: equal when nothing was
   recompiled, a strict superset after a dependency's [Admitted -> Qed].

   Absence from that table means an empty closure, because the table has an
   entry for every constant and inductive of that library's environment with
   a non-empty closure ([library_roots]); so the object must be one of them:
   it is in the global environment under that library's path, and its user
   and canonical names agree. That rules out a copy made through a module
   alias or an [Include] of a plain module, whose canonical name stays its
   origin's: such a copy is walked, and its body leads to the original. A
   copy made by a functor application or an [Include] of one has agreeing
   names, and is a root of its own library's table ([library_roots] lists
   every constant the environment holds under the library's path), so its
   stored closure is the one that library computed for it. A library without
   a table (compiled without -location-free-label, or whose closures could
   not be computed) is walked.

   Two traits of [Assumptions.traverse] make what a walk reaches depend on the
   order it visits objects in, which one walk for every root does not
   reproduce per root: a match on an empty type over an axiom marks the axiom
   reached without walking its type, and an object is skipped when one with
   the same user name is reached, whatever its canonical name. Either raises
   [Full_walk], and so does a cycle among objects, which the walk's graph
   should never hold; the caller then computes every closure by
   [closure_of]. *)
let fast_closures ~stored access self roots =
  let env = Global.env () in
  let tables = Hashtbl.create 17 in
  let table dp =
    match Hashtbl.find_opt tables dp with
    | Some t -> t
    | None ->
      let t = Option.map (fun a ->
          let h = Hashtbl.create (List.length a) in
          List.iter (fun (name, ks) -> Hashtbl.replace h name (SSet.of_list ks)) a;
          h) (stored dp) in
      Hashtbl.add tables dp t;
      t
  in
  let stored_closure gr =
    let found = match gr with
      | GlobRef.ConstRef c
        when KerName.equal (Constant.user c) (Constant.canonical c) && Environ.mem_constant c env ->
        Some (Constant.modpath c, Constant.to_string c)
      | GlobRef.IndRef (m, _) | GlobRef.ConstructRef ((m, _), _)
        when KerName.equal (MutInd.user m) (MutInd.canonical m) && Environ.mem_mind m env ->
        Some (MutInd.modpath m, MutInd.to_string m)
      | GlobRef.ConstRef _ | GlobRef.IndRef _ | GlobRef.ConstructRef _ | GlobRef.VarRef _ -> None
    in
    match found with
    | None -> None
    | Some (mp, name) ->
      match mpfile_root mp with
      | Some dp when not (DirPath.equal dp self) ->
        Option.map (fun h -> Option.default SSet.empty (Hashtbl.find_opt h name)) (table dp)
      | Some _ | None -> None
  in
  let stopped = ref 0 in
  let stop gr = Option.has_some (stored_closure gr) && (incr stopped; true) in
  let graph, empty_match = Assumptions.reach ~stop access (List.map snd roots) in
  if empty_match then raise (Full_walk "a match on an empty type over an axiom");
  (* The key [graph] holds each user name under, and each block's members. *)
  let keyed = GlobRef.Map_env.mapi (fun k _ -> k) graph in
  let blocks = GlobRef.Map_env.fold (fun k v acc ->
      match k with
      | GlobRef.IndRef (m, _) | GlobRef.ConstructRef ((m, _), _) ->
        Mindmap_env.update m (fun l -> Some ((k, v) :: Option.default [] l)) acc
      | GlobRef.ConstRef _ | GlobRef.VarRef _ -> acc)
      graph Mindmap_env.empty in
  let value gr =
    match GlobRef.Map_env.find_opt gr keyed with
    | Some k when GlobRef.CanOrd.equal k gr -> GlobRef.Map_env.find gr graph
    | Some _ -> raise (Full_walk "two canonical names under one user name")
    | None -> raise (Full_walk "a reference the walk did not reach")
  in
  let own gr v = SSet.of_list (keys (Assumptions.object_assumptions gr v)) in
  let memo = ref GlobRef.Map_env.empty and memo_blocks = ref Mindmap_env.empty in
  let active = ref GlobRef.Set_env.empty and active_blocks = ref Mindmap_env.Set.empty in
  let rec closure gr =
    match stored_closure gr with
    | Some s -> s
    | None ->
      match gr with
      | GlobRef.IndRef (m, _) | GlobRef.ConstructRef ((m, _), _) -> block_closure m gr
      | GlobRef.ConstRef _ | GlobRef.VarRef _ ->
        match GlobRef.Map_env.find_opt gr !memo with
        | Some s -> s
        | None ->
          let v = value gr in
          if GlobRef.Set_env.mem gr !active then raise (Full_walk "a cycle");
          active := GlobRef.Set_env.add gr !active;
          let edges = match v, gr with
            | Some refs, _ -> refs
            | None, GlobRef.ConstRef c -> Assumptions.type_references c
            | None, (GlobRef.VarRef _ | GlobRef.IndRef _ | GlobRef.ConstructRef _) ->
              GlobRef.Set_env.empty
          in
          let s = GlobRef.Set_env.fold (fun e acc -> SSet.union (closure e) acc) edges (own gr v) in
          active := GlobRef.Set_env.remove gr !active;
          memo := GlobRef.Map_env.add gr s !memo;
          s
  (* Every member of a block is reached with the block, with the block's
     references (less its first inductive) as its value. *)
  and block_closure m gr =
    match Mindmap_env.find_opt m !memo_blocks with
    | Some s -> s
    | None ->
      let v = value gr in
      if Mindmap_env.Set.mem m !active_blocks then raise (Full_walk "a cycle");
      active_blocks := Mindmap_env.Set.add m !active_blocks;
      let members = Option.default [] (Mindmap_env.find_opt m blocks) in
      let members_own = List.fold_left (fun acc (k, kv) -> SSet.union (own k kv) acc) SSet.empty members in
      let edges = Option.default GlobRef.Set_env.empty v in
      let same_block = function
        | GlobRef.IndRef (m', _) | GlobRef.ConstructRef ((m', _), _) -> MutInd.UserOrd.equal m m'
        | GlobRef.ConstRef _ | GlobRef.VarRef _ -> false
      in
      let s = GlobRef.Set_env.fold (fun e acc ->
          if same_block e then acc else SSet.union (closure e) acc) edges members_own in
      active_blocks := Mindmap_env.Set.remove m !active_blocks;
      memo_blocks := Mindmap_env.add m s !memo_blocks;
      s
  in
  let per_root = List.filter_map (fun (name, root) ->
      match SSet.elements (closure root) with
      | [] -> None
      | keys -> Some (name, keys)) roots in
  if debug then
    Printf.eprintf "[keepfacts] %s: %d roots, one walk of %d objects, %d foreign stored closures\n%!"
      (DirPath.to_string self) (List.length roots) (GlobRef.Map_env.cardinal graph) !stopped;
  per_root

let compute_assumptions ~stored access self =
  try
    let env = Global.env () in
    let st = Conv_oracle.get_transp_state (Environ.oracle env) in
    let roots = library_roots self in
    let every_walk why =
      if debug then
        Printf.eprintf "[keepfacts] %s: %d roots, each by its own walk (%s)\n%!"
          (DirPath.to_string self) (List.length roots) why;
      List.filter_map (fun (name, root) ->
          match closure_of access st root with
          | [] -> None
          | keys -> Some (name, keys))
        roots
    in
    let per_root =
      if full_walk then every_walk "ROCQ_KEEPFACTS_FULL_WALK=1"
      else match fast_closures ~stored access self roots with
        | per_root -> per_root
        | exception Full_walk why -> every_walk why
        | exception e when CErrors.noncritical e -> every_walk (Printexc.to_string e)
    in
    Some (List.sort (fun (a, _) (b, _) -> String.compare a b) per_root)
  with e when CErrors.noncritical e -> None

(* Keyed by the constant's user name, the name [LibkeyObjects.axiom_report]
   lists it under in the library that holds it (an [Include] copy has its own
   entry there, with the status of its copied body), with that library: the
   [MPfile] root of the user name, which a dotted string cannot give back.

   A query is kept when the constant is foreign, and also, for a body read,
   when the table it read is foreign though the constant is this library's:
   a copy made here of another library's opaque proof (a functor application
   or an [Include] of one, at any depth, a sealed module whose implementation
   is such an expression) reads that library's table, by an extraction or by
   the closure walk ([logging_access]).

   A constant recorded more than once keeps [opaque = true] if any record has
   it, and the table of its body read. The records of one compile agree but
   in one case: an extraction that reads the opaque proof of a sealed module's
   implementation records it as an opaque body read
   ([Extraction.extract_constant]) while the global environment, and so a
   strategy command or the extraction's first record, sees the signature's
   axiom. A body read is the stronger fact: the keep rule keeps the dependent
   only when the holder's object and the table's object are both
   byte-identical. *)
let collect_opacity self =
  let tbl = Hashtbl.create 16 in
  List.iter
    (fun (c, opaque, table) ->
      let mp = Constant.modpath c in
      let foreign_table = match table with
        | Some dp -> not (DirPath.equal dp self)
        | None -> false
      in
      if not (is_self self mp) || foreign_table then
        let key = Constant.to_string c in
        let opaque, table = match Hashtbl.find_opt tbl key with
          | Some (_, seen, seen_table) ->
            (seen || opaque), (match seen_table with Some _ -> seen_table | None -> table)
          | None -> opaque, table
        in
        Hashtbl.replace tbl key (Option.map DirPath.to_string (mpfile_root mp), opaque, table))
    (OpacityLog.get ());
  Hashtbl.fold (fun k (lib, v, table) acc ->
      { constant = k; library = lib; opaque = v; table = Option.map DirPath.to_string table } :: acc)
    tbl []
  |> List.sort (fun a b -> String.compare a.constant b.constant)

(* The accessor the closures are computed with: [access], which also logs each
   opaque body the walk reads, for a constant of this library, from another
   library's opaque table, as a body-read query ([OpacityLog.record_body_read]:
   that constant, opaque, the table's library).

   Why. The walk reads a body in another library's table for this library's
   copy of a proof: a functor application at any depth, an [Include] of one,
   and a sealed [Module X : T := L.F A], whose constants the walk reads from
   the expression ([Assumptions.lookup_constant_in_impl]) and which holds no
   reference the compiled form shows when [T] omits the proof. The closure
   stored for that copy then depends on the table's library: an edit there
   that keeps its label (an opaque proof that starts using an axiom) changes
   the copy's real closure, and a dependent that took the stored one would
   miss the axiom. The query makes the keep rule require that library's
   object byte-identical to keep this one, as for an extraction body read.

   What is not logged. A body in this library's own table (this library
   recomputes it on every compile). A foreign constant's body: the full walk
   (ROCQ_KEEPFACTS_FULL_WALK=1, or the fallback) reads every one it reaches,
   and the stored-closure walk reads one only for a library that stored no
   closures, or for a copy whose user and canonical names differ (an alias,
   or an [Include] of a plain module, which it enters; such a copy is a
   transparent definition, so its walk reaches the original). Neither walk
   logs them: their holder is a dependency, whose own keepfacts log its
   copies, and whose closures the keep rule's monotone condition checks. So
   both walks log the same queries, since both walk every constant of this
   library they reach.

   A fresh accessor per library also starts the walks' reuse afresh
   ([Assumptions] keys it by the accessor), so no entry made before, which
   logged nothing, is replayed in place of a read. *)
let logging_access self (access : Global.indirect_accessor) : Global.indirect_accessor =
  let note o =
    match Assumptions.reading_constant () with
    | Some c when is_self self (Constant.modpath c) ->
      let (_, _, dp, _) = Opaqueproof.repr o in
      if not (DirPath.equal dp self) then OpacityLog.record_body_read c o
    | Some _ | None -> ()
  in
  { Global.access_proof = (fun o -> note o; access.Global.access_proof o);
    access_uncooked_proof = (fun o -> note o; access.Global.access_uncooked_proof o) }

let compute ~access ~stored ~self =
  (* The closures first: their walk logs body reads [collect_opacity] reads
     (the order a record's fields are evaluated in is unspecified). *)
  let assumptions = compute_assumptions ~stored (logging_access self access) self in
  { assumptions; opacity_queries = collect_opacity self }
