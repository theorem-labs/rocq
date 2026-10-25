(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Checking opaque proofs in forked worker processes.

    The check of an opaque body is handed to [defer], and the read of
    one library's table of opaque proofs to [defer_table]. By default
    each is run immediately. With [-j N] for [N > 1], it is queued
    instead, and queued jobs are run in batches by worker processes
    created with [Unix.fork]: up to [N-1] while the main process carries
    on with the rest of the libraries, then up to [N] while it waits for
    them in [finish], where it checks nothing itself. A worker inherits a
    copy-on-write copy of the whole heap, so it runs the queued closures
    as they are: nothing is marshalled and nothing is shared afterwards.

    A batch is checked only if its worker exits with code 0. It is a run
    of the queue: the jobs of one library are next to each other there,
    so a batch holds whole libraries, the libraries next to it go to
    other workers, and one process parses each table once.

    A worker lives for at most a time budget (see [set_budget]): the
    longer a worker lives, the more of the heap it shares with the main
    process it has copied. Once the budget has passed, and the worker
    has completed at least one job, it stops after the job it is in
    and reports how many jobs of its batch, the first ones in order, it
    completed. The main process queues the others again, at the front.

    A worker also stops that way on request. When the main process has
    dealt everything and a worker slot is free, it asks the worker with the
    largest batch, with SIGUSR1, to give back the jobs it has not
    started; it asks each worker at most once, and never a batch of one
    job. The worker answers with a release message saying how many
    jobs it will complete, which is at least one. The main process reads
    that message at once and deals the others to the free slots, instead
    of leaving them behind a long check in a batch that a busy worker
    holds. The worker then stops after the job it is in, and its final
    report must equal the number it announced.

    So every job is run exactly once, by a process that ends
    successfully, whichever way the work is cut into batches. *)

val set_jobs : profiling:bool -> int -> unit
(** [set_jobs ~profiling n] allows [n] processes to check at the same
    time: the main one and [n-1] workers while the libraries are
    checked, then [n] workers. It has no effect when [n <= 1], and falls
    back to checking in the main process, with a warning, when profiling
    or when [Unix.fork] is not available. *)

val parallel : unit -> bool
(** Whether a deferred job is queued for a worker process, which is
    [-j N] for [N > 1] where [set_jobs] did not fall back to checking
    sequentially. When it is false, [defer] and [defer_table] run their
    closure at once, in the main process, and nothing else ever will. *)

val default_budget : float
(** Seconds. *)

val set_budget : float -> unit
(** [set_budget t] makes workers stop after [t] seconds of wall time,
    counted from their creation, at the next end of a check, but never
    before one check is completed. [t = 0.] makes a worker complete a
    single check. @raise Invalid_argument if [t] is negative or NaN. *)

type job =
| Proof of Names.Constant.t
| Table of Names.DirPath.t
(** What a process is given to do: check the body of one opaque constant,
    or read one library's table of opaque proofs. *)

exception CheckError of job * exn
(** A deferred job raised an exception. Only raised when jobs are
    deferred, i.e. not with [-j 1]. *)

val set_error_printer : (exn -> unit) -> unit
(** How a worker reports the [CheckError] it caught, before it exits. *)

val defer : Names.Constant.t -> (unit -> unit) -> unit
(** [defer kn check] runs or queues the check of the opaque body of
    [kn]. [check] must not depend on anything that happens after it
    is queued, nor have effects that anything else depends on. [defer]
    reaps the workers that have exited, so it can raise [WorkerFailed]
    as [finish] does. *)

val defer_table : Names.DirPath.t -> (unit -> unit) -> unit
(** [defer_table dp read] runs or queues the read of the table of opaque
    proofs of the library [dp], and opens the group of the jobs that
    [defer] takes next: they are the checks of that library, and a batch
    takes them together with this one. *)

val note_cook : unit -> unit
(** Called by the cook of an opaque body ([Mod_checking]): counts it when
    it runs outside a worker, so in the main process. With [-j] that is a
    sealed module's constant, whose cooked body the main process needs,
    and a check that the main process ran itself because it could not
    fork. The count is printed by [-d checker-workers]. *)

val note_table_read : bytes:int -> unit
(** Counts one table of opaque proofs read and parsed by this process, and
    the bytes it read for it, for the debug output. *)

val finish : unit -> unit
(** Deal everything that is still queued to workers and wait for all of
    them. Raises [WorkerFailed] if a worker did not exit with code 0, did
    not report between 1 and [size] completed checks, wrote a malformed
    release message or more than one, or completed a number of checks other
    than the one its release message named. *)

val abort : unit -> unit
(** Kill all workers, wait for them, and drop the queued checks. *)

val table_checked : Names.DirPath.t -> bool
(** Whether a process that ended successfully read the table of opaque
    proofs of this library: the main process, or a worker whose report
    says it completed that read. *)

type batch = {
  size : int;
  first : job;
  last : job;
  proofs : int;
  first_proof : Names.Constant.t option;
  last_proof : Names.Constant.t option;
}
(** A worker's jobs: [size] of them from [first] to [last], of which
    [proofs] are checks of opaque proofs, from [first_proof] to
    [last_proof]. *)

exception WorkerFailed of int * Unix.process_status * batch
(** A worker (pid, status) failed while checking the given batch. The
    other workers have been killed. The error the worker printed is held
    until [print_held_output] or [drop_held_output]. *)

val print_held_output : unit -> unit
(** Print to standard error what the worker whose [WorkerFailed] was
    raised last printed after its error, and forget it. *)

val drop_held_output : unit -> unit
(** Forget it, without printing it. *)

val pr_batch : batch -> Pp.t
(** The opaque proofs of a batch, in stock's words: "N opaque proofs (the
    first is X, the last Y)". *)

val pr_doing : job -> Pp.t
(** What a process doing this job is doing, as "checking the opaque proof
    of X" or "reading the opaque proofs of X". *)

val signal_name : int -> string

(** {2 For tests only} *)

val default_report_writer : Unix.file_descr -> int -> unit
(** What a worker does to report the number of checks it completed. *)

val set_report_writer : (Unix.file_descr -> int -> unit) -> unit
(** [set_report_writer f] replaces what a worker does to report the number
    of checks it completed, given the descriptor to write to. *)

val min_batch : int
(** The size below which no batch is dealt while the libraries are
    checked, but for one whose lane ran short, of at least [min_batch / 2]:
    the expected batches of a test depend on it. *)

val set_window : float -> unit
(** [set_window w]: while the libraries are checked, [defer] deals at
    most once every [w] seconds (1 by default). A test sets it to
    [infinity], so that only [end_window] makes [defer] deal. *)

val end_window : unit -> unit
(** The next [defer] or [defer_table] deals, as once a window has passed. *)
