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
  (** Each foreign constant (its user name) a non-opaque
      [Strategy]/[Transparent] command in this library named, with the opacity
      it saw ([true]: the constant was an opaque proof; [false]: it was not).
      Sorted by name. The keep rule rebuilds a dependent when the recorded
      opacity no longer matches the dependency's current one -- the command
      would then error, or stop erroring, on a real recompile. *)
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

let closure_of access st root =
  let (theory, m) =
    Assumptions.assumptions ~add_opaque:false ~add_transparent:false access st [root] in
  let acc =
    Printer.ContextObjectMap.fold (fun k _ acc -> context_object_key k :: acc) m [] in
  let flag name b acc = if b then ("theory:" ^ name) :: acc else acc in
  let acc = flag "impredicative_set" theory.Printer.has_impredicative_set acc in
  let acc = flag "rewrite_rules" theory.Printer.has_rewrite_rules acc in
  let acc = flag "type_in_type" theory.Printer.has_type_in_type acc in
  let acc = flag "unchecked_eliminations" theory.Printer.has_unchecked_eliminations acc in
  List.sort_uniq String.compare acc

let compute_assumptions access self =
  try
    let env = Global.env () in
    let st = Conv_oracle.get_transp_state (Environ.oracle env) in
    let per_root =
      List.filter_map (fun (name, root) ->
          match closure_of access st root with
          | [] -> None
          | keys -> Some (name, keys))
        (library_roots self) in
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

let compute ~access ~self =
  { assumptions = compute_assumptions access self;
    opacity_queries = collect_opacity self }
