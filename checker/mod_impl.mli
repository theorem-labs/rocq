(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** What a module's implementation declares, where the environment holds an
    interface instead. See mod_impl.ml. *)

val defines_constant : Environ.env -> Names.Constant.t -> bool
(** Does the implementation give this constant a body? [false] where it
    declares it as a parameter or an axiom, and where the walk cannot read
    the implementation, so that a caller that reports assumed constants keeps
    every name it is unsure of. *)
