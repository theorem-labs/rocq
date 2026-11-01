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

(** Whether a constant was an axiom or an opaque proof when a command whose
    outcome depends on that distinction ran while a library was compiled (a
    non-opaque [Strategy]/[Transparent] command, an extraction, a
    [Functional Scheme], a plugin's [Global.body_of_constant]), and which
    opaque table a proof body was read from (an extraction,
    [Global.body_of_constant], the keepfacts closure walk) (all of them
    kept in one log file), from every process that compiles it: the
    compiling one, its [par:] and [-async-proofs] workers, and the children
    a plugin forks, for the records a child writes before the library is
    saved. See [opacityLog.ml] for why and how. *)

type query = {
  constant : string;  (** the constant's user name *)
  library : string option;  (** the [MPfile] root of its user name; [None] for a functor parameter's *)
  opaque : bool;  (** [true] for an opaque proof or a body read *)
  table : string option;  (** for a body read, the library whose opaque table holds the body *)
}

val env_var : string
(** ["ROCQ_OPACITYLOG_FILE"]: the path of the log file, which a worker
    captures at startup and clears from its environment. The worker pool sets
    it again only when it starts another Rocq worker. *)

val identity_env_var : string
(** ["ROCQ_OPACITYLOG_IDENTITY"]: the device and inode, as decimal numbers
    separated by [:], of the log file {!env_var} names. It is an integrity
    check, not a secret: in-process native code is not an isolation boundary.
    A worker captures it with {!env_var}, clears both variables, and forwards
    them explicitly only to another Rocq worker. The worker pool removes both
    variables from inherited and extra environments. *)

val set_enabled : bool -> unit
(** [set_enabled true]: collect the queries of this compilation.
    [Library.set_location_free_label] calls it, before any tactic runs: the
    queries are collected only under [-location-free-label]. This process
    then creates its log inside a private 0700 directory in TMPDIR, through
    an [O_CREAT|O_EXCL] descriptor (it never reopens a temporary path). Its
    path is absolute even when TMPDIR is relative, so a later change of
    directory does not change which file the path names. It records the
    device and inode of that descriptor; if the log cannot be made, {!get}
    answers [None]. At exit it removes the log and its private directory;
    another uid cannot enter that directory, and code of this uid is not an
    isolation boundary. The compiling process clears any inherited values of
    {!env_var} and {!identity_env_var}; the worker pool gives workers
    {!worker_env_value} and {!worker_identity_env_value} from this process's
    retained descriptor instead. Worker processes are not
    given the flag, so they never call [set_enabled true]; a worker
    ([Flags.async_proofs_is_worker]) uses the values it captured at startup
    when it opens the log on its first record, only when its device and inode
    equal those in {!identity_env_var}. *)

val worker_env_value : unit -> string
(** The value of {!env_var} a worker this process spawns must get: the log
    this process has open (the owner's, a worker's, or a forked child's),
    else, in a worker that has not opened it yet, the value it captured at
    startup, and [""] (no log: the worker records nothing) otherwise.
    [AsyncTaskQueue.spawn] sets it in place of any inherited or extra-env
    entry. *)

val worker_identity_env_value : unit -> string
(** The value of {!identity_env_var} that accompanies {!worker_env_value}:
    the device and inode of its open log, or, in a worker that has not opened
    it yet, the value it captured at startup, and [""] otherwise. *)

val reset : unit -> unit
(** Forget the queries logged so far, and, if this process created the log
    file, empty it through its own descriptor and write the log's first line
    again. *)

val record : Constant.t -> Declarations.constant_body -> unit
(** [record c cb]: such a command told [c], whose body is [cb], apart as an
    axiom or an opaque proof. Logs [c] with [opaque = true] when [cb]'s body
    is an opaque proof ([OpaqueDef]), [opaque = false] when it is
    [Undef None], and nothing for any other body. It is kept in memory when
    this process collects queries, and appended to the log file by the only
    processes that append: the owner, a worker (the log {!env_var} names) and
    a forked child of either (the descriptor it inherited). A worker or child
    that cannot open the log or write the record raises an error, before the
    caller uses the answer it records. *)

val record_body_read : Constant.t -> Opaqueproof.opaque -> unit
(** [record_body_read c o]: an extraction, a caller of
    [Global.body_of_constant], or the walk that computes the library's
    assumption closures ([KeepFacts]), read the body of [c], the opaque proof
    [o]. Logs [c] with [opaque = true] and [table] the library whose opaque
    table holds that body ([Opaqueproof.repr o]), also when it is the library
    holding [c]. Kept and appended as {!record} does. *)

val get : unit -> query list option
(** The queries logged so far, with repeats: those the log file holds (every
    process's) and those of this process. [None] when the log could not be
    created, opened, written or read back, when the file its path names now
    is not the one this process created (another device or inode: another
    file put there, even an empty one or a copy of its bytes), when it does
    not start with the log's first line (it was emptied), holds a line that
    is not a record, or does not end with a newline (a torn last line): the
    caller then stores no opacity queries at all. These checks do not detect
    a rewrite of the log's own file that keeps its first line (only a
    process that can write the file can make one; the processes that log
    only append), see [opacityLog.ml]. *)

val encode_line : query -> string
(** The line, newline included, a query is written to the log as: tab
    separated, ["R"], the constant, the library, ["1"] or ["0"] for
    [opaque], the table; each name in hexadecimal (two lowercase digits a
    byte), an absent library or table as ["-"] and a present one as ["+"]
    followed by its digits. A name can therefore hold any byte, a tab or a
    newline among them (an identifier made by [Names.Id.of_string_soft]),
    and distinct queries give distinct lines. *)

val decode_line : string -> query option
(** The query a line (without its newline) of the log holds, or [None] for
    a line that {!encode_line} does not write: [decode_line] is the inverse
    of {!encode_line} and refuses every other spelling, an empty constant
    included. *)
