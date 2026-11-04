(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Typed removal of source locations, for the location-free interface key
    of a library (see [Libobject.interface_key]).

    A {e stripper} for a type ['a] is a function ['a -> 'a] written against
    the type: it returns a copy of its argument in which every field of type
    [Loc.t] holds {!fixed} and every field of type [Loc.t option] holds
    [None], and in which nothing else differs. A stripper never inspects the
    runtime shape of a value, so it cannot erase a value that only looks like
    a location. Values are only copied for the key: the objects that a
    library stores keep their locations. *)

exception Unknown of string
(** Raised by a stripper that reaches a value it cannot strip by type, such
    as a generic argument or an extension with no registered stripper. The
    string names what it reached. The library then has no interface key
    (no label: it gets stock's digest). *)

val unknown : string -> 'a
(** [unknown what] raises [Unknown what]. *)

val fixed : Loc.t
(** The fixed value that replaces a field of type [Loc.t]. *)

val loc : Loc.t -> Loc.t
(** Always {!fixed}. *)

val loc_opt : Loc.t option -> Loc.t option
(** Always [None]. *)

val cast : ('a -> 'b) -> 'a CAst.t -> 'b CAst.t
(** Strip the location of the node and map its value. *)

val dast : ('a -> 'b) -> ('a, 'c) DAst.t -> ('b, 'c) DAst.t
(** Same for a [DAst] node; a delayed value is forced. *)

val located : ('a -> 'b) -> 'a Loc.located -> 'b Loc.located
(** Same for a [Loc.located] pair. *)
