(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Names made of identifiers.

    [rocqchk -compare] compares the printed names of the axioms that a proof
    reaches with the axiom names that its config permits, and writes them in
    its verdict. These names come from the libraries the checker loads. A
    name that is not made of identifiers ([Names.Id.is_valid]), for instance
    one that holds a line break or a blank, is not one that Rocq's own
    commands write, but a plugin or a modified file can write it. The
    comparator's closure ([Check_closure]) refuses such a printed name, so a
    name that holds a line break or a blank cannot be mistaken for the
    printed name of a permitted axiom. *)

open Names

val valid_id : Id.t -> bool
(** The identifier is one that [Names.Id.is_valid] accepts. *)

val valid_kername : KerName.t -> bool
(** Every component of the name that [KerName.to_string] prints is an
    identifier: each component of the library path, the identifier and
    every path component of a functor parameter, each module label and the
    last label. *)

val quote : string -> string
(** A refused name in an error message: between double quotes, with
    [String.escaped]. *)
