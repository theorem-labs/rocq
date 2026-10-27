(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Native evaluation, inside the bytecode machine, of binary-number operations
    that the machine would otherwise interpret one digit at a time.

    The machine recognises an operation by its definition, never by its name.
    [pin_of_constant] accepts a constant only when the computational skeleton of
    its body, of the bodies of every constant that body uses, and the
    declarations of the inductive types it matches on, are exactly the ones the
    native code implements. A constant that merely carries the name of a
    standard operation is evaluated as it is written, by the stock path. *)

val pin_of_constant : Environ.env -> Names.Constant.t -> Vmbytecodes.znative_op option

val pinned : unit -> int
(** How many constants this process has given a native implementation to. *)

val encoding : Environ.env -> Names.Constant.t -> string option
(** The canonical encoding of the constant's definition closure, which
    [pin_of_constant] compares against the expected ones. Exposed so that a test
    can print it and so that the expected strings can be regenerated when the
    standard library changes. *)
