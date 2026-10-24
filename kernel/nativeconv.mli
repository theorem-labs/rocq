(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Constr
open Conversion

(** This module implements the conversion test by compiling to OCaml code *)

val native_conv : conv_pb -> Genlambda.evars -> types kernel_conversion_function

(** [native_cast_conv] is [native_conv] for the casts of
    [Typeops.check_cast] while [Nativecode.native_vm_conversion ()]
    holds, except that it returns [None], after a
    [native-conversion-failed] warning, when the OCaml compiler or the
    dynamic linker failed on the unit of the conversion. Nothing of that
    unit is then linked, and the caller decides the cast another way. *)
val native_cast_conv : conv_pb -> Genlambda.evars -> Environ.env -> types -> types ->
  (unit, unit) Result.t option

(** A conversion function parametrized by a universe comparator. Used outside of
    the kernel. *)
val native_conv_gen : conv_pb -> Genlambda.evars -> Environ.env -> ('a, 'err) generic_conversion_function

val w_native_disabled : CWarnings.warning
