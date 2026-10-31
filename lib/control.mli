(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global control of Rocq. *)

(** Used to convert signals to exceptions *)
exception Timeout

(** Will periodically call [Thread.delay] if set to true *)
val enable_thread_delay : bool ref

val interrupt : bool ref
(** Rocq interruption: set the following boolean reference to interrupt Rocq
    (it eventually raises [Break], simulating a Ctrl-C) *)

val check_for_interrupt : unit -> unit
(** Use this function as a potential yield function. If {!interrupt} has been
    set, il will raise [Sys.Break]. *)

val timeout : float -> ('a -> 'b) -> 'a -> ('b, Exninfo.info) result
(** [timeout n f x] tries to compute [Ok (f x)], and if it fails to do
    so before [n] seconds, returns [Error info] instead (where [info]
    contains the backtrace of the timeout exception). *)

type timeout_counts = { armed : int; fired : int }

val timeout_counts : unit -> timeout_counts
(** How many timeouts {!timeout} armed in this process, and how many of them
    expired. Both only grow. *)

val add_timeout_counts : timeout_counts -> unit
(** Add to this process's counts the counts of another process, so that a
    master can report the timeouts its workers armed. *)

val deadline : float -> ('a -> 'b) -> 'a -> ('b, Exninfo.info) result
(** {!timeout} for a limit the build driver puts on the whole compilation
    from outside, such as the proof replay budget (BET-84), which stands in
    for the driver's own per-file kill. It is not a timeout of the file:
    {!timeout_counts} does not count it, and it does not make the open proof
    ineligible for replay. *)

(** Set a particular timeout function; warning, this is an internal
   API and it is scheduled to go away. *)
type timeout = { timeout : 'a 'b. float -> ('a -> 'b) -> 'a -> ('b,Exninfo.info) result }
val set_timeout : timeout -> unit

(** [protect_sigalrm f x] computes [f x], but if SIGALRM is received during that
    computation, the signal handler is executed only once the computation is
    terminated. Otherwise said, it makes the execution of [f] atomic w.r.t.
    handling of SIGALRM.

    This is useful for example to prevent the implementation of `Timeout` to
    interrupt I/O routines, generating ill-formed output.

*)
val protect_sigalrm : ('a -> 'b) -> 'a -> 'b
