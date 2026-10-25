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

(* A kernel name the recorder printed, read back. [Nametab.global_of_path]
   finds what that absolute path names now; the printed name must come out
   the same, so a path that names something else is not taken for it.

   [Absent] is a name nothing is bound to now. A lookup of it finds
   nothing, which is a value the record can hold ([null]), so a proof that
   read a constant that this compile deleted still replays, where
   [Unknown] would have refused it. *)
type 'a parsed = Found of 'a | Absent | Unreadable

let global_of_string s =
  match Nametab.global_of_path (Libnames.path_of_string s) with
  | g -> Found g
  | exception Not_found -> Absent
  | exception _ -> Unreadable

let constant_of_string s =
  match global_of_string s with
  | Found (GlobRef.ConstRef c) when String.equal (Constant.to_string c) s -> Found c
  | Found _ -> Unreadable
  | Absent -> Absent
  | Unreadable -> Unreadable

let mind_of_string s =
  match global_of_string s with
  | Found (GlobRef.IndRef (mind, _)) when String.equal (MutInd.to_string mind) s -> Found mind
  | Found (GlobRef.ConstructRef ((mind, _), _)) when String.equal (MutInd.to_string mind) s -> Found mind
  | Found _ -> Unreadable
  | Absent -> Absent
  | Unreadable -> Unreadable

let modpath_of_string s =
  match Nametab.locate_module (Libnames.qualid_of_string s) with
  | mp when String.equal (ModPath.to_string mp) s -> Found mp
  | _ -> Unreadable
  | exception Not_found -> Absent
  | exception _ -> Unreadable

(* Census row 1: the globals the proof looked up. The value comes from the
   SAME function the recorder called at the lookup ([Environ.recorded_*]),
   never from a second computation here: a channel computed two ways is
   how a replay would accept a changed input. *)
let row1 () =
  let of_key parse recorded key =
    match parse key with
    | Unreadable -> Proof_replay.Unknown
    | Absent -> Proof_replay.Value None
    | Found k ->
      (match recorded k (Global.env ()) with
       | v -> Proof_replay.Value v
       | exception _ -> Proof_replay.Unknown)
  in
  let c = of_key constant_of_string and m = of_key mind_of_string and p = of_key modpath_of_string in
  Proof_replay.register_evaluator "constant" (c Environ.recorded_constant);
  Proof_replay.register_evaluator "constant_exists" (c Environ.recorded_constant_exists);
  Proof_replay.register_evaluator "rewrite_rules" (c Environ.recorded_rewrite_rules);
  Proof_replay.register_evaluator "inductive" (m Environ.recorded_inductive);
  Proof_replay.register_evaluator "inductive_exists" (m Environ.recorded_inductive_exists);
  Proof_replay.register_evaluator "module" (p Environ.recorded_module);
  Proof_replay.register_evaluator "modtype" (p Environ.recorded_modtype)

(* Rows 5, 7 and 15 register their evaluators beside their one value
   function ([Reductionops.ReductionBehaviour], [Hints], [Rocqlib]), so the
   recorder and the evaluator cannot call two implementations. *)
let tables () = ()

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
