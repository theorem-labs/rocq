(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Proof replay for one compile (BET-84, part P3): the steps of
    [rocq compile -proof-replay FILE] (or [-proof-replay-dir DIR]). The
    compile configures replay from its command line, starts it before the
    file runs, and writes the summary at its end. The record is loaded
    and bound by {!Proof_replay_record}, the source is scanned by
    {!Proof_replay_scan}, and each proof is decided by {!Proof_replay}. *)

val configure :
  source:Proof_replay_record.source -> ratio:float -> budget:float option ->
  peak_limit_kb:int option -> digest:string option -> unit
(** The command line's options. Call before the compile. It makes
    {!Proof_recorder.in_use} true, gives [source], [peak_limit_kb] and
    [digest] to {!Proof_replay_record.configure}, and [ratio] and [budget]
    to the charged clock ({!Proof_replay.configure_clock}). There is no
    default ratio: [-proof-replay] without [-proof-replay-ratio] is a usage
    error. *)

val configured : unit -> bool
(** Whether {!configure} was called. *)

val set_vo_path : string -> unit
(** The [.vo] this compile writes, as its command line gives it. With
    [-proof-replay-dir], its path relative to the working directory is one
    of the places the record is looked for. Call it before {!start}. *)

val start :
  library:string -> source:string option -> toolchain:(unit -> Proof_record.toolchain) -> unit
(** Loads the record for this library ({!Proof_replay_record.load}), scans
    the source file [source] for late commands
    ({!Proof_replay_scan.late_events}) and starts the file's state and
    clock ({!Proof_replay.start}). A no-op when no source is configured.
    After it, {!Proof_replay.refused} says whether the whole file runs
    without replay, and why. In a file with a command after its first
    [Qed] or [Save] that can rebind a Rocqlib name or load code, every
    proof that opens before the last such command runs its tactics
    (outcome [ineligible], channel ["rebind"]), and the summary's
    [refused_detail] names the first command and its line; a [Require]
    counts only while a library it names is not loaded at the proof's
    opening. An unreadable source is refused whole (reason ["rebind"]). *)

val write_summary : string -> unit
(** Writes [<base>.proof-replay.json] (see {!summary_path_of_vo}): the
    counts this compile reached ({!Proof_replay.summary}), for the grading
    engine's metadata. A no-op when no source is configured. *)

val summary_path_of_vo : string -> string
(** [summary_path_of_vo "dir/Foo.vo"] is ["dir/Foo.proof-replay.json"]. *)

val killed_summary : string -> unit
(** {!write_summary} for a compile the charged clock killed. *)
