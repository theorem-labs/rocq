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
open Environ
open Constr


val globref_of_string : string -> Names.GlobRef.t option
(** A reference read back from the string [GlobRef.print] writes: a
    constant or variable as its path, an inductive as ["(path, i)"], a
    constructor as ["(path, i, j)"]. [None] when it does not read back,
    so that a replay never takes one reference for another (BET-84 P3). *)
val rename_arguments : bool -> GlobRef.t -> Name.t list -> unit

(** [Not_found] is raised if no names are defined for [r] *)
val arguments_names : env -> GlobRef.t -> Name.t list

val rename_type : env -> types -> GlobRef.t -> types

val rename_typing : env -> constr -> unsafe_judgment
(** Typechecks using the kernel [Typeops.infer] *)
