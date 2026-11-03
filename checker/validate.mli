(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Analyze

val validate : Values.value -> data * obj LargeArray.t -> unit

val check : Values.value -> data * obj LargeArray.t -> (unit, string) result
(** [validate] that prints nothing: [Error] says what failed and where. For a
    reader whose standard output is a document ([rocq-library-label]). *)
