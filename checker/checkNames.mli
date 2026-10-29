(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The names the checker prints must be made of identifiers.

    The checker prints names that it reads from the libraries it loads: in its
    progress lines, in the context summary of [-o] and in the report of
    [-statement-report]. A name that is not an identifier
    ([Names.Id.is_valid]), for instance one that holds a line break or a
    blank, could add a line of its own to that output. Rocq's own commands
    write no such name, but a plugin or a modified file can, so the checker
    refuses one rather than print it: [CheckLibrary] when it reads a library,
    and [Check_closure] for a name that only a term of an admitted library
    holds. *)

open Names

val valid_id : Id.t -> bool

val valid_dirpath : DirPath.t -> bool
(** Every component of the path is an identifier. *)

val valid_mbid : MBId.t -> bool
(** The identifier of the functor parameter and every component of its path,
    which [MBId.to_string] prints. *)

val valid_kername : KerName.t -> bool
(** Every component of the name that [KerName.to_string] prints. *)

val quote : string -> string
(** A refused name in an error message: between double quotes, with
    [String.escaped]. *)
