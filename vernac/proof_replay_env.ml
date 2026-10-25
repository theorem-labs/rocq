(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* What a recorded read is worth now (BET-84, part P3). One evaluator per
   channel of the census. An evaluator answers [Unknown] rather than
   guessing: the proof then runs its tactics, as today. *)

open Names

let digest what v =
  match Proof_record.digest_value v with
  | d -> Proof_replay.Value (Some d)
  | exception Proof_record.Unhashable _ -> ignore what; Proof_replay.Unknown

let absent = Proof_replay.Value None

(* A kernel name the recorder printed, read back. [Nametab.global_of_path]
   finds what that absolute path names now; the printed name must come out
   the same, so a path that names something else is not taken for it. *)
let global_of_string s =
  match Nametab.global_of_path (Libnames.path_of_string s) with
  | g -> Some g
  | exception _ -> None

let constant_of_string s =
  match global_of_string s with
  | Some (GlobRef.ConstRef c) when String.equal (Constant.to_string c) s -> Some c
  | _ -> None

let mind_of_string s =
  match global_of_string s with
  | Some (GlobRef.IndRef (mind, _)) when String.equal (MutInd.to_string mind) s -> Some mind
  | Some (GlobRef.ConstructRef ((mind, _), _)) when String.equal (MutInd.to_string mind) s -> Some mind
  | _ -> None

let modpath_of_string s =
  match Nametab.locate_module (Libnames.qualid_of_string s) with
  | mp when String.equal (ModPath.to_string mp) s -> Some mp
  | _ -> None
  | exception _ -> None

(* Census row 1: the globals the proof looked up. The value comes from the
   SAME function the recorder called at the lookup ([Environ.recorded_*]),
   never from a second computation here: a channel computed two ways is
   how a replay would accept a changed input. *)
let row1 () =
  let of_key parse recorded key =
    match parse key with
    | None -> Proof_replay.Unknown
    | Some k -> (match recorded k (Global.env ()) with v -> Proof_replay.Value v | exception _ -> Proof_replay.Unknown)
  in
  let c = of_key constant_of_string and m = of_key mind_of_string and p = of_key modpath_of_string in
  Proof_replay.register_evaluator "constant" (c Environ.recorded_constant);
  Proof_replay.register_evaluator "constant_exists" (c Environ.recorded_constant_exists);
  Proof_replay.register_evaluator "rewrite_rules" (c Environ.recorded_rewrite_rules);
  Proof_replay.register_evaluator "inductive" (m Environ.recorded_inductive);
  Proof_replay.register_evaluator "inductive_exists" (m Environ.recorded_inductive_exists);
  Proof_replay.register_evaluator "module" (p Environ.recorded_module);
  Proof_replay.register_evaluator "modtype" (p Environ.recorded_modtype)

(* Row 5: how [simpl] unfolds a constant. Row 7: the hint database a
   search read. Row 15: the registered library references. *)
let tables () =
  Proof_replay.register_evaluator "reduction_behaviour" (fun key ->
      match constant_of_string key with
      | None -> Proof_replay.Unknown
      | Some c -> digest "reduction_behaviour" (Reductionops.ReductionBehaviour.get c));
  Proof_replay.register_evaluator "hint_db" (fun key ->
      match Hints.searchtable_map key with
      | db -> digest "hint_db" db
      | exception Not_found -> absent);
  Proof_replay.register_evaluator "lib_ref" (fun key ->
      match Rocqlib.lib_ref_opt key with
      | None -> absent
      | Some r -> digest "lib_ref" r)

(* The reads that have no single read point: the universe and quality
   graphs, the named context, the typing flags, the options, and, with
   -proof-record-tables, every hint database and typeclass table at the
   proof's start. Both sides take them from the same function, so they
   cannot drift apart. *)
let providers () =
  Proof_replay.register_provider Proof_record_env.start_reads;
  Proof_replay.register_provider Proof_recorder.table_reads

let init () =
  row1 ();
  tables ();
  providers ()
