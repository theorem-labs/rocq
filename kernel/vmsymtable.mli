(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* $Id$ *)

open Constr
open Environ
open Vmvalues

val val_of_constr : env -> Genlambda.evars -> constr -> Vmvalues.values

val set_link_recorder : (Names.Constant.t -> unit) -> unit
(** [set_link_recorder f] registers [f] to be called with each constant
    whose VM global is freshly linked by [val_of_constr] in this process.
    It observes only; it does not change any value. Inert by default. *)

val vm_interp : tcode -> values -> vm_env -> int -> values
