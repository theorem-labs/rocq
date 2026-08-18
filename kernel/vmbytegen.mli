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
  body_code

type lazy_body_code =
  | LBCdefined of (env -> (bool array * to_patch * patches) option)
  | LBCalias of Names.Constant.t
  | LBCconstant
  | LBCuncompiled

val classify_constant_body : fail_on_error:bool ->
  env -> universes -> (Constr.t, 'opaque, 'symb) constant_def ->
  lazy_body_code
(** [compile_constant_body] split in two: everything that decides which code
    descriptor a constant gets, and the compilation proper, returned as a thunk.
    A constant is compiled iff it yields [LBCdefined], so a caller can reserve
    its VM slot without compiling it. The environment of the compilation is
    given back at that point, so that a caller deferring it need not retain the
    one classification was done in. Used by the checker. *)

(** Shortcut of the previous function used during module strengthening *)

val compile_alias : Names.Constant.t -> 'a pbody_code

(** Dump the bytecode after compilation (for debugging purposes) *)
val dump_bytecode_flag : CDebug.flag
