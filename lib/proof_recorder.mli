(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The runtime that collects a {!Proof_record} file during one compile
    (BET-84, part P2).

    [rocq compile -proof-record] calls {!start} once, and {!write} after the
    [.vo]. Between them, the choke points of the channel census call
    {!read}, {!ineligible} and {!without_recording}, and the proof
    lifecycle calls {!open_proof} and {!close_proof}.

    {b The recorder is off unless [start] was called.} Then every function
    here returns at once, computes none of its arguments and allocates
    nothing, so a compile without the option behaves as one built without
    this file. The same holds between proofs: a read outside a proof is
    dropped without computing its key or its value.

    Not thread-safe: one compile process, one record. [rocq compile] runs
    its proofs in one domain when async proofs are off, which is the
    registration's mode. *)

val active : unit -> bool
(** Whether a proof is open and its reads are being recorded. False when
    the recorder is off, between proofs, and inside {!without_recording}. *)

val current_name : unit -> string option
(** The name of the open proof, if any. *)

val generation : unit -> int
(** A number that changes at each {!open_proof}. A hot choke point keeps
    its own memo of the keys it already recorded, and empties it when this
    number changes, so that it digests each key once per proof instead of
    once per lookup. *)

(** {6 The compile} *)

val start :
  library:string ->
  source:string ->
  source_digest:string ->
  toolchain:(unit -> Proof_record.toolchain) ->
  skip_qed_typecheck:bool ->
  tables_at_start:bool ->
  unit
(** Turns the recorder on and starts the file's clocks. [toolchain] is
    called now for the header, and at each proof's start for its
    [toolchain_key] (a [Require] moves it). With [tables_at_start], each
    proof's [start_tables] is filled from the functions given to
    {!register_tables}. *)

val register_tables : (unit -> Proof_record.read list) -> unit
(** Adds a source of start-of-proof table digests (hint databases, typeclass
    tables). Called at each proof's start, and only when the compile ran
    with [tables_at_start]. A no-op otherwise, so its argument is never
    called. *)

val write : string -> unit
(** Writes the record to that path and turns the recorder off. Call it
    after the [.vo], so that a compile that fails leaves no record. A no-op
    when the recorder is off. *)

val stop : unit -> unit
(** Turns the recorder off and drops what it holds, with no file. *)

(** {6 Proofs} *)

val open_proof :
  name:string ->
  statement:(unit -> string) ->
  position:Proof_record.position ->
  unit
(** Starts an entry. While a proof is open, a second [open_proof] (an
    [abstract] sub-proof, a nested obligation) writes no entry of its own:
    it marks the open proof ineligible with reason ["nested_proof"], and
    its reads are kept as the open proof's own. *)

val sentence : (unit -> string) -> (unit -> 'a) -> 'a
(** [sentence digest run] runs one parsed sentence. When a proof is open at
    the end of [run], or was opened by it, [digest ()] is kept as one of
    the proof's sentences (key item 1, the statement's sentence included).
    [digest] is called only then. *)

val close_proof : closer:string -> kernel_check:bool -> unit
(** Ends the entry of the innermost open proof and, at the outermost one,
    appends it to the record, with the sentences and the writes collected
    since {!open_proof}. [kernel_check] says whether the kernel typed the
    proof at this closer. Call it after the declaration, inside
    {!without_recording}. *)

(** {6 Writes} *)

val writing : unit -> bool
(** Whether a proof is open, inside {!without_recording} too. A write call
    site tests this first, so that a compile without the option builds no
    write argument. *)

val write_universes : levels:string list -> constraints:string list -> unit
val write_scheme : string -> unit
val write_constraint_source : string -> unit
val write_warning : name:string -> message:string -> unit
val write_counters : (string * int) list -> unit
(** What the proof changed for the proofs after it. They are collected
    while a proof is open, {!without_recording} included, because a write
    made by the declaration at the closer is still the proof's write.
    {!write_counters} gives the total advance of each counter; calling it
    twice for one counter adds the two. *)

(** {6 Reads} *)

val read :
  row:string ->
  channel:string ->
  key:(unit -> string) ->
  value:(unit -> string option) ->
  unit
(** Records one read of census row [row] on [channel]. [key] and [value]
    are called only when a proof is open, so a choke point pays only one
    test when the recorder is off. Only the first read of a key in a proof
    is kept, and a repeat computes neither its value nor any digest: the
    global state moves inside a proof only through the proof's own writes
    or through a command or sub-proof that makes it ineligible. *)

val read_by :
  row:string ->
  channel:string ->
  id:'a ->
  key:(unit -> string) ->
  value:(unit -> string option) ->
  unit
(** {!read} for a hot choke point: a repeat is found by [id], a raw name
    compared structurally (a kernel name, a qualid), so neither [key] nor
    [value] is called for it. [id] must determine [key]. *)

val ineligible : reason:string -> detail:string -> unit
(** Marks the open proof ineligible. Repeating a (reason, detail) pair adds
    nothing. A no-op when no proof is open. *)

val digest : ?locs:Loc.source -> what:string -> 'a -> string
(** {!Proof_record.digest_value} of a value that the recorder must digest
    to go on. A value it cannot digest is not an error: the result is
    ["unhashable"] and the open proof is marked ineligible with reason
    ["unhashable"] and detail [what], so the proof runs as today. *)

val digest_cached : what:string -> 'a -> string
(** {!digest} of a value of the global environment, kept for the whole
    compile and keyed by the value's address. A constant's body is one
    value for every proof that reads it, so it is digested once per file,
    not once per proof. Never call it on a value that is rebuilt at each
    read: that fills the cache and digests every copy. *)

val without_recording : (unit -> 'a) -> 'a
(** Runs [f] with reads dropped, and restores the previous state, also when
    [f] raises. The [Qed] kernel check runs inside this, so the read set of
    a registration compile (which types the proof) equals the read set of a
    grade compile (which does not, under [-skip-qed-typecheck]). *)
