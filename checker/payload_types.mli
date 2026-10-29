(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val payloads : string
(** The payload part of [rocq-library-label --vo-representation]: the OCaml
    type of what every object kind of this build stores in a .vo, with the
    definition of every type that reaches, and what could not be read. The
    implementation is written at build time by checker/vo_payloads.ml, from
    the typed trees of the directories this executable links (checker/dune);
    that file says what the printing covers. *)
