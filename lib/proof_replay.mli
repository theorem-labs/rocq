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
  source:source -> ratio:float -> budget:float option -> peak_limit_kb:int option ->
  digest:string option -> unit
(** The command line's options. Call before the compile.

    {b The record is a trusted input, at the same tier as the binary.} Its
    stored terms are read back with [Marshal.from_string], which is not
    memory-safe on chosen bytes, and a stored term's declared type comes
    from it, so the record's parser is NOT a security boundary. A record is
    used only when it is bound to this compile: its bytes hash (SHA-256) to
    [digest] when one is given (the grading engine passes the digest from
    the registration's root-owned manifest), the compiling user cannot
    write it and nobody but its owner can, and its header names this
    library. Otherwise the whole file runs as stock and the summary names
    the reason ([digest], [writable], [library], [format]). *)

val configured : unit -> bool

exception Budget_exhausted
(** The charged clock reached the budget. The compile writes no [.vo] and
    exits as a killed file. *)

(** {6 The compile} *)

val start :
  library:string -> source:string option -> toolchain:(unit -> Proof_record.toolchain) -> unit
(** Loads the record for this library and starts the clock. A no-op when no
    source is configured. After it, {!refused} says whether the whole file
    runs without replay, and why. [toolchain] is this compile's: a record
    whose header names another binary, plugin set, load order,
    safe-dependency set or stack limit is refused for the whole file, before
    any of its proofs is declared (reason ["toolchain"]). In a file with a
    command after its first [Qed] or [Save] that can rebind a Rocqlib name or
    load code, every proof that opens before the last such command runs its
    tactics (outcome [ineligible], channel ["rebind"]), and [refused_detail]
    names the first command and its line; a [Require] counts only while a
    library it names is not loaded at the proof's opening. An unreadable
    source is refused whole (reason ["rebind"]). *)

val scan_late_rebind : string -> (string * int) option
(** The first command in this source text, after its first [Qed] or [Save],
    that can rebind a Rocqlib name or load code — [Register], [Require],
    [Load], [Declare], [Import], [Export], [Include], [Module], or an [End]
    that closes a module or a section inside which one of those appeared —
    with its line; [None] if there is none. Comments and strings are
    skipped; a number is read as Rocq's lexer reads it, and a late word also
    counts at the end of a longer identifier. A component of a qualified
    identifier ([Module.module_contents], [M.Register]) is one identifier
    token to the lexer and is not a late word. *)

val scan_late_events : ?imports_late:bool -> string -> (string * int) option * int option
(** {!scan_late_rebind}, and the byte offset of the LAST such command's
    word. With [~imports_late:false], [Import] and [Export] are not late. A
    plain module ([Module M.], [Module Import M.]) is not late by itself,
    and its [End] only when a late word appeared inside it. *)

type require_text = { rq_from : string option; rq_names : string list }
(** A [Require] the source text spells out in full: its [From] prefix and
    its library names, as written. *)

type late_command = { lc_offset : int; lc_require : require_text option }
(** A late command: its word's byte offset, and for a [Require] the text
    spells out in full, that [Require]. *)

val scan_late_commands : ?imports_late:bool -> string -> (string * int) option * late_command list
(** {!scan_late_rebind}, and every late command, last first. A [Require]
    carries its names when it is its sentence's command word, or follows
    the sentence's [From q], and its sentence is [From q]? [Require]
    [(safe)]? ([Import] or [Export], with import categories)? then names
    of plain ASCII identifiers, each with an import filter or not. *)

val register_require_resolver : (string option -> string list -> (unit -> bool) option) -> unit
(** [f from names] resolves a [Require] as the [Require] itself will
    resolve it, warning about nothing: [None] when a name does not resolve,
    else a test of whether every library it names is loaded. Until one
    registers, no [Require] resolves, so each one is late. *)

val note_export_register : unit -> unit
(** An export-locality Rocqlib registration was loaded or declared: from now
    on, [Import] and [Export] are late commands. *)

val note_require : already_loaded:bool -> unit
(** A [Require] runs; [already_loaded]: every library it names was loaded
    before it. Listed in the summary. A [Require] that loads a library
    after a proof of this file was replayed raises an anomaly: that replay
    relied on no later [Require] loading one. *)

val at_sentence : Loc.t -> unit
(** The location of the sentence the toplevel is about to run. *)

val close_proof : unit -> unit
(** A proof ended (its closer or its [Abort]). A proof opened inside another
    one is part of it: it is not counted, and its end only closes it. *)

val proof_open : unit -> bool
(** Whether a proof is open, as {!open_proof} and {!close_proof} count. *)

val drop_all_proofs : unit -> unit
(** The proof stack holds no proof any more ([Abort All], [Reset], a
    [Succeed] around a statement): no proof is open from now on, and the
    candidate, if any, is abandoned. *)

val register_plugin_audit : (string -> bool) -> unit
(** [f name] says whether the loaded ML plugin [name] (a findlib package) is
    one this tree builds. While a plugin [f] rejects is loaded, no proof is
    replayed (counted ineligible; the summary's [fence] names it). Until a
    predicate registers, every plugin is unaudited, except the plugins from
    outside the tree that replay itself lists as audited
    ([rocq-read-file.plugin]). *)

val register_hit_hook : (Proof_record.read list -> unit) -> unit
(** [f reads] runs at each hit with the replayed proof's recorded reads, so
    the owner of a process-wide cache can count them as looked up. *)

val set_vo_path : string -> unit
(** The [.vo] this compile writes, as its command line gives it. With
    [-proof-replay-dir], its path relative to the working directory is one
    of the places the record is looked for. Call it before {!start}. *)

val register_precheck : (string -> bool) -> unit
(** A last check on the stored term, run at the closer and before any
    tactic: the layer that made the blob says whether this compile can
    use it (the universe counters it was made from). A blob that fails it
    is a miss on key item 1. *)

val register_install_check : (string -> (string * string) option) -> unit
(** [f blob] runs at the closer once every recorded read gave its value
    again: the layer that made the blob puts together what the declaration
    takes from it (a term it refers to in the registered [.vo], a universe
    state it rebuilds) and checks it against what the registration
    declared. [Some (channel, why)] is a read miss on that channel, for
    that reason; an exception is a miss on ["stored_term"]. *)

val registered_object : unit -> (string * string option) option
(** The registration's [.vo], beside the loaded record under the same name,
    and the SHA-256 of its opaque proofs that the record's trailer holds
    ({!Proof_record.trailer.vo_opaques}). [None] with no record loaded. *)

val remaining_budget : unit -> float option
(** What is left of the budget once the charge for the replayed proofs is
    taken off, or [None] with no budget. A sentence runs under this as a
    timeout, so a proof that runs long is stopped inside it, where stock's
    own timeout stops it, and not only at the next sentence boundary. *)

val enabled : unit -> bool
(** A record is loaded and the file is not refused. *)

val refused : unit -> string option
(** The reason the whole file runs without replay: ["memory"] (the recorded
    peak is above the limit), ["rlimit"], ["overcommit"], ["bad_record"], or
    ["rebind"] for a source the late-command scan cannot read. A late
    command keeps only the proofs before it from replaying. *)
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
    the miss, and charges the clock on a hit. Once a process-wide fence has
    tripped ({!Proof_recorder.fence_tripped}), every proof from then on is
    refused and counted as ineligible, and the summary's [fence] names the
    first trip. *)

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

val register_summary_counter : string -> unit
(** A counter kept in the Summary, which the STM rolls back when a proof
    closes: replay leaves it where it is, as stock's rollback does, and a
    proof that moved it can still be replayed. The next proof's
    [counter_start] read checks that the rollback came out the same. *)

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
