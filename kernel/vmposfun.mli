(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (c)   **************************************************************)
(*    \\//    *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(************************************************************************)

(** Validate a kernel registration for a bytecode VM operation on [positive]. *)
val check : Environ.env -> Retroknowledge.pos_function -> Names.Constant.t -> unit
val bind : Environ.env -> Names.Constant.t -> Vmvalues.values -> unit
