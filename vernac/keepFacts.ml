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
  opaque : bool;  (** whether it was an opaque proof when the command ran *)
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
      ([opaque = true]); a constant of any other body form is not recorded.
      Sorted by name. The keep rule rebuilds a dependent when the recorded
      opacity no longer matches the dependency's current one -- the command
      could then error, or stop erroring, on a real recompile. *)
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
   segment [Library] read with the library's other segments): the objects
   reachable from it are that library's and its dependencies', the same
   objects then and now, so it is the same set. Absence from that table means
   an empty closure, because the table has an entry for every constant and
   inductive of that library's environment with a non-empty closure
   ([library_roots]); so the object must be one of them: it is in the global
   environment under that library's path, and its user and canonical names
   agree, which rules out a copy made through a module alias, an [Include] or
   a functor (those are walked, their bodies lead to the originals). A library
   without a table (compiled without -location-free-label, or whose closures
   could not be computed) is walked.

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
   [MPfile] root of the user name, which a dotted string cannot give back. *)
let collect_opacity self =
  let tbl = Hashtbl.create 16 in
  List.iter
    (fun (c, opaque) ->
      let mp = Constant.modpath c in
      if not (is_self self mp) then
        Hashtbl.replace tbl (Constant.to_string c)
          (Option.map DirPath.to_string (mpfile_root mp), opaque))
    (OpacityLog.get ());
  Hashtbl.fold (fun k (lib, v) acc -> { constant = k; library = lib; opaque = v } :: acc) tbl []
  |> List.sort (fun a b -> String.compare a.constant b.constant)

let compute ~access ~stored ~self =
  { assumptions = compute_assumptions ~stored access self;
    opacity_queries = collect_opacity self }
