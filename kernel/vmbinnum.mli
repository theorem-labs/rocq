(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Functions on binary numbers that the bytecode VM runs as C routines.

    The bytecode compiler asks {!recognize} about the body of each constant.
    When the body is equal to a reference term of this module (up to binder
    names, the printing annotation of matches, and the inductive types, which
    may be any types of the expected shape), the compiler puts the
    instruction [BINNUM k n] at the start of the code of the function, after
    its entry sequence. A constant that a reference calls must itself have a
    body equal to the reference of that callee (read from the environment
    each time, through aliases). Routine [k] (kernel/byterun/rocq_binnum.c)
    then computes the result when every node of the arguments that it reads
    is a constructor of the expected type, and leaves every other call to the
    bytecode. It reads at least the nodes that the bytecode reads.

    Environment variables, for tests and measurement only, read when this
    module is loaded:
    - [ROCQ_VM_BINNUM=0] turns recognition off; [ROCQ_VM_BINNUM=-name1,-name2]
      turns off the listed routines. Any other value stops the process.
    - [ROCQ_VM_BINNUM_STATS=1] prints, at the exit of each process, the
      calls, refusals and words read of each routine, in total, at function
      entry and at call sites; the constants bound and the near misses of the
      recognizer at function entry; and the counts of the recognitions at
      call sites. [2] also prints, for each near miss at function entry, the
      first node that differs from the reference. When the variable is unset,
      the routines count nothing. *)

val recognize : ?name:Names.Constant.t -> Environ.env -> Constr.t -> int -> int option
(** [recognize ?name env body] is, for each function index [i] of the
    top-level fixpoint block of [body] (index 0 for a body that is a
    function), the routine of the function, if [body] is equal to a
    reference term and every inductive type in it has the expected shape in
    [env]. It never raises. [name] is only printed in the statistics. *)

val recognize_call : Environ.env -> Names.Constant.t -> int option
(** [recognize_call env cst] is the routine of the function that [cst]
    denotes, for a call site of [cst]: [cst] must be a transparent definition
    with an empty universe context in [env], and its body must be recognized
    as by {!recognize}. The function is the one at the init index of a
    fixpoint body, or the body itself. It never raises. *)

val no_binnum : int -> int option
(** No routine for any function. *)

val arity : int -> int
(** The number of arguments of a routine. *)

val reset_stats : unit -> unit
(** Zeroes the counters, in a process forked from one that has used them. *)

val print_stats : unit -> unit
(** Prints the counters on stderr if [ROCQ_VM_BINNUM_STATS] is set. The
    process prints them at exit by itself; this is for processes that end
    with [Unix._exit]. *)
