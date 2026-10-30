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

val levers_on : bool
(** Whether this process generates the code the VM levers of this build produce:
    the compile-time expansion of a small called constant's body (the
    [inline_limit] below, which {!Vmsymtable} sets from this) and the native
    binary-number operations of {!Vmznative}. False under ROCQ_VM_INLINE=0,
    where the process generates the code its base generates.

    The native operations are pinned while a declaration is compiled, so with
    this false a library file carries different bytecode, and a process runs the
    bytecode the library files it loads carry: an arm that is to generate and run
    the base's code must build its libraries under the switch too. *)

(** [inline_limit] (default 0, no inlining) is the size under which an applied constant's body is
    expanded instead of called; see [Genlambda.inlinable_body]. Code that goes into a library file
    is compiled with the default, so a library's bytes do not depend on this limit (they do depend
    on [levers_on], through the native operations above). *)
val compile :
  fail_on_error:bool ->
  ?inline_limit:int ->
  env -> Genlambda.evars -> constr ->
  (bool array * to_patch * patches) option
(** In every compiled term, a call of a constant with as many arguments as
    the routine that {!Vmbinnum.recognize_call} gives it goes through
    BINNUMCALL first. *)

val compile_constant_body : ?name:Names.Constant.t -> ?count:bool -> fail_on_error:bool ->
  ?inline_limit:int ->
  env -> universes -> (Constr.t, 'opaque, 'symb) constant_def ->
  body_code option
(** The code of a constant's body. When {!Vmbinnum.recognize} binds the body
    to routines, the code of each bound function starts with BINNUM; calls
    in the body go through BINNUMCALL as in {!compile}. [name] is only
    printed in the statistics of {!Vmbinnum}, and [count] is passed to
    {!Vmbinnum.recognize}: a body compiled again in one process is not
    counted again. *)

(** Shortcut of the previous function used during module strengthening *)

val compile_alias : Names.Constant.t -> 'a pbody_code

(** Dump the bytecode after compilation (for debugging purposes) *)
val dump_bytecode_flag : CDebug.flag
