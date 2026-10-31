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

val vm_interp : tcode -> values -> vm_env -> int -> values

(** How many constants this process has compiled again, with small bodies expanded, instead of
    running the code their library file carries. *)
val compiled_again : unit -> int

val recorded_vm_global : ?on_call:(Names.Constant.t -> unit) -> env -> Names.Constant.t -> string option
(** BET-84: the value of a [vm_global] read of a constant: a digest of its
    bytecode without its place in the library's code table, or absent.
    [on_call] receives each constant that code calls. *)
