(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Replaying a proof's stored term (BET-84, part P3).

    [rocq compile -proof-replay FILE] (or [-proof-replay-dir DIR]) reads the
    record a registration compile wrote ({!Proof_record}) and, at each proof
    whose key matches and whose every recorded read gives the same value
    now, declares the stored term instead of running the tactics.

    {b Every uncertainty is a miss.} A record that does not parse, a key
    item that differs, a read on a channel with no evaluator, an evaluator
    that cannot answer, a proof the registration marked ineligible, a proof
    that stored no term: each makes this proof run its tactics, as today.
    The only way a stored term is used is a full match.

    {b The charged clock.} A replayed proof costs almost no time, where
    stock would have spent its registered wall seconds. So the compile
    charges itself [ratio] times each replayed proof's registered wall
    seconds, on top of the time it really spent, and raises
    {!Budget_exhausted} when the total reaches the per-file budget. [ratio]
    is the grade-to-registration ratio of per-file wall time, taken at the
    top of its measured spread, so near the budget replay is only ever
    stricter than stock (GRADE, 2026-10-24 08:15Z). There is no default:
    [-proof-replay] without [-proof-replay-ratio] is a usage error. *)

type source =
  | Record_file of string  (** one record file, for this compile only *)
  | Record_dir of string
      (** a directory of records: the file's record is
          [DIR/<dotted logical name>.proof-record.jsonl], or
          [DIR/<the same with dots turned into slashes>.proof-record.jsonl]. *)

val configure :
  source:source -> ratio:float -> budget:float option -> peak_limit_kb:int option -> unit
(** The command line's options. Call before the compile. *)

val configured : unit -> bool

exception Budget_exhausted
(** The charged clock reached the budget. The compile writes no [.vo] and
    exits as a killed file. *)

(** {6 The compile} *)

val start : library:string -> unit
(** Loads the record for this library and starts the clock. A no-op when no
    source is configured. After it, {!refused} says whether the whole file
    runs without replay, and why. *)

val set_vo_path : string -> unit
(** The [.vo] this compile writes, as its command line gives it. With
    [-proof-replay-dir], its path relative to the working directory is one
    of the places the record is looked for. Call it before {!start}. *)

val register_precheck : (string -> bool) -> unit
(** A last check on the stored term, run at the closer and before any
    tactic: the layer that made the blob says whether this compile can
    use it (the universe counters it was made from). A blob that fails it
    is a miss on key item 1. *)

val enabled : unit -> bool
(** A record is loaded and the file is not refused. *)

val refused : unit -> string option
(** The reason the whole file runs without replay: ["memory"] (the recorded
    peak is above the limit), ["rlimit"], ["overcommit"], ["bad_record"]
    (missing or unreadable), or [None]. *)

val check_budget : unit -> unit
(** Raises {!Budget_exhausted} when the elapsed time plus the charge has
    reached the budget. Call it at each sentence. *)

val write_summary : string -> unit
(** Writes [<base>.proof-replay.json] (see {!summary_path_of_vo}): the
    counts this compile reached, for the grading engine's metadata. A no-op
    when no source is configured. *)

val summary_path_of_vo : string -> string
(** [summary_path_of_vo "dir/Foo.vo"] is ["dir/Foo.proof-replay.json"]. *)

val killed_summary : string -> unit
(** {!write_summary} for a compile the charged clock killed. *)

(** {6 One proof} *)

val open_proof :
  name:string ->
  statement:(unit -> string) ->
  position:(unit -> Proof_record.position) ->
  toolchain_key:(unit -> Proof_record.toolchain_key) ->
  unit
(** Called where the recorder's [open_proof] is. It looks the proof up by
    name and keeps it as the open candidate when its name, statement,
    position and toolchain key all match and it stored a term. The
    arguments are computed only when a record is loaded. *)

val candidate_open : unit -> bool
(** Whether the open proof has a candidate: the sentences and the closer
    are still to come. *)

val decide : sentences:string list -> closer:string -> string option
(** The decision at the closer, before any tactic ran. [Some blob] is the
    stored term; [None] means the proof runs its tactics. Counts the hit or
    the miss, and charges the clock on a hit. *)

val abandon : unit -> unit
(** Drops the open candidate without a decision: the proof ran as stock. *)

(** {6 Read evaluators} *)

type evaluation =
  | Unknown  (** this evaluator cannot answer: the proof misses *)
  | Value of string option  (** the digest the lookup gives now, or absent *)

val register_evaluator : string -> (string -> evaluation) -> unit
(** [register_evaluator channel f] makes [f key] the value of a recorded
    read on [channel]. A channel with no evaluator makes every proof that
    read it miss, counted under that channel's name. *)

val register_provider : (unit -> Proof_record.read list) -> unit
(** A provider gives, as one list, the reads of the channels that have no
    single read point, from the same function the recorder takes them
    from. A recorded read whose channel a provider covers, but which the
    provider does not list now, is a miss. *)

val register_counter : string -> get:(unit -> int) -> set:(int -> unit) -> unit
(** A process-wide counter whose advance a proof's record holds (census
    row 18). A replayed proof's tactics never move it, so replay reads it
    at the proof's start and {!apply_counters} puts it at start plus the
    recorded advance. A counter nothing registers cannot be moved, so a
    proof that moved it is never replayed. The universe and sort counters
    are not registered: the stored term carries them. *)

val apply_counters : unit -> unit
(** Puts each counter of the proof just replayed where its tactics would
    have left it. Call it after the declaration. A no-op with no hit. *)

val provide : channel:string -> key:string -> value:string option -> unit
(** The value of one read of the proof being opened, known only to the code
    that opens it (the proof's own [Proof using] set). Call it after
    {!open_proof}; it holds for that proof only. *)

val channel_misses : unit -> (string * int) list
(** How many proofs each channel cost, highest first. The summary carries
    it, so a channel worth an evaluator is visible. *)

(** {6 The stored term} *)

val set_pending : string option -> unit
(** The stored term the closer about to run must declare in place of the
    proof's own. The declaration takes it with {!take_pending}; the caller
    clears it afterwards, so a closer that took another path never leaves
    one behind. *)

val take_pending : unit -> string option

val encode_blob : string -> string
(** Base64 of a [Marshal] blob, for {!Proof_record.proof.replay}: the
    record is JSON, which carries no arbitrary bytes. *)

val decode_blob : string -> string option
(** The inverse, [None] on a string that is not base64. *)
