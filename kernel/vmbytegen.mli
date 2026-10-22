(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vmemitcodes
open Constr
open Declarations
open Environ

val compile :
  fail_on_error:bool ->
  env -> Genlambda.evars -> constr ->
  (bool array * to_patch * patches) option

val compile_constant_body : fail_on_error:bool ->
  env -> universes -> (Constr.t, 'opaque, 'symb) constant_def ->
  body_code option

(** As {!compile_constant_body}, but the bytecode of a transparent constant is
    compiled lazily (a [BCdeferred] thunk) on first use rather than now. The
    checker uses this so the library walk does not compile bytecode the check
    may never touch; the thunk yields the same result as the eager function. *)
val compile_constant_body_deferred : fail_on_error:bool ->
  env -> universes -> (Constr.t, 'opaque, 'symb) constant_def ->
  body_code option

(** Shortcut of the previous function used during module strengthening *)

val compile_alias : Names.Constant.t -> 'a pbody_code

(** Dump the bytecode after compilation (for debugging purposes) *)
val dump_bytecode_flag : CDebug.flag
