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

    The check of an opaque body is handed to [defer]. By default it is
    run immediately. With [-j N] for [N > 1], it is queued instead, and
    queued checks are run in batches by up to [N-1] worker processes
    created with [Unix.fork], while the main process carries on with
    the rest of the libraries. A worker inherits a copy-on-write copy
    of the whole heap, so it runs the queued closures as they are:
    nothing is marshalled and nothing is shared afterwards.

    A batch is checked only if its worker exits with code 0. *)

val set_jobs : profiling:bool -> int -> unit
(** [set_jobs ~profiling n] allows [n] processes to check at the same
    time: the main one and [n-1] workers. It has no effect when
    [n <= 1], and falls back to checking in the main process, with a
    warning, when profiling or when [Unix.fork] is not available. *)

exception CheckError of Names.Constant.t * exn
(** The deferred check of the body of a constant raised an exception.
    Only raised when checks are deferred, i.e. not with [-j 1]. *)

val set_error_printer : (exn -> unit) -> unit
(** How a worker reports the [CheckError] it caught, before it exits. *)

val defer : Names.Constant.t -> (unit -> unit) -> unit
(** [defer kn check] runs or queues the check of the opaque body of
    [kn]. [check] must not depend on anything that happens after it
    is queued, nor have effects that anything else depends on. *)

val finish : unit -> unit
(** Check everything that is still queued and wait for all workers.
    Raises [WorkerFailed] if a worker did not exit with code 0. *)

val abort : unit -> unit
(** Kill all workers, wait for them, and drop the queued checks. *)

type batch = {
  size : int;
  first : Names.Constant.t;
  last : Names.Constant.t;
}

exception WorkerFailed of int * Unix.process_status * batch
(** A worker (pid, status) failed while checking the given batch. The
    other workers have been killed. *)

val pr_batch : batch -> Pp.t

val signal_name : int -> string
