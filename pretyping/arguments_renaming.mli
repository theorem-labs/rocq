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

val rename_arguments : bool -> GlobRef.t -> Name.t list -> unit

(** The renaming table as it stands; [same_table] is physical identity, so a table changed since is not the same. *)
type table
val current_table : unit -> table
val same_table : table -> table -> bool

(** [Not_found] is raised if no names are defined for [r] *)
val arguments_names : env -> GlobRef.t -> Name.t list

val rename_type : env -> types -> GlobRef.t -> types

val rename_typing : env -> constr -> unsafe_judgment
(** Typechecks using the kernel [Typeops.infer] *)
