(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The resource limits of the running process, as strings for the proof
    record (BET-84, census row 24). Each function reads a Linux file and
    answers ["unknown"] when it cannot. They are never an error: a compile
    on another kernel records ["unknown"] and goes on. *)

val rlimit : string -> string
(** [rlimit "Max stack size"] is the soft limit of that row of
    [/proc/self/limits]: ["unlimited"], a decimal byte count, or
    ["unknown"]. The row names are the kernel's own, for example
    ["Max stack size"], ["Max address space"], ["Max data size"]. *)

val memory_cap : unit -> string
(** The cgroup v2 memory cap of the process ([memory.max] of its cgroup):
    ["max"], a decimal byte count, or ["unknown"]. Recorded, never part of
    a key: the registration and the grade run under different caps. *)

val overcommit_memory : unit -> string
(** [/proc/sys/vm/overcommit_memory]: ["0"], ["1"], ["2"] or ["unknown"].
    With ["2"] an allocation can fail before any cap is reached, so replay
    is refused. *)

val peak_rss_kb : unit -> int
(** The process's peak resident set in kB ([VmHWM] of
    [/proc/self/status]), or 0 when it cannot be read. *)
