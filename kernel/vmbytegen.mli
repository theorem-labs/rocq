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

(** [inline_limit] (default 0, no inlining) is the size under which an applied constant's body is
    expanded instead of called; see [Genlambda.inlinable_body]. Code that goes into a library file
    is compiled with the default, so a library's bytes do not depend on it. *)
val compile :
  fail_on_error:bool ->
  ?inline_limit:int ->
  env -> Genlambda.evars -> constr ->
  (bool array * to_patch * patches) option
(** In every compiled term, a call of a constant with as many arguments as
    the routine that {!Vmbinnum.recognize_call} gives it goes through
    BINNUMCALL first. *)

val compile_constant_body : ?name:Names.Constant.t -> fail_on_error:bool ->
  ?inline_limit:int ->
  env -> universes -> (Constr.t, 'opaque, 'symb) constant_def ->
  body_code option
(** The code of a constant's body. When {!Vmbinnum.recognize} binds the body
    to routines, the code of each bound function starts with BINNUM; calls
    in the body go through BINNUMCALL as in {!compile}. [name] is only
    printed in the statistics of {!Vmbinnum}. *)

val compile_znative_wrapper :
  Names.Constant.t -> Vmbytecodes.znative_op -> to_patch * patches
(** Code for [fun x y => op x y], the value the machine gives a constant whose
    definition [Vmznative] recognises. When an argument is not a closed number
    the operation applies the value of the constant instead, so such a call
    reduces exactly as it does without the native path. *)

(** Shortcut of the previous function used during module strengthening *)

val compile_alias : Names.Constant.t -> 'a pbody_code

(** Dump the bytecode after compilation (for debugging purposes) *)
val dump_bytecode_flag : CDebug.flag
