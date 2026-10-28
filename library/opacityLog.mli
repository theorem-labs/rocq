(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** The opacity a non-opaque [Strategy]/[Transparent] command saw on a
    constant while a library was compiled (design D18, dispatch://INFRA-361).
    See [opacityLog.ml] for why. *)

val set_enabled : bool -> unit
(** Log queries ([true]) or ignore every [record] call ([false], the default).
    [Library.set_location_free_label] sets it: the queries are collected only
    under [-location-free-label]. *)

val reset : unit -> unit
(** Forget the queries logged so far. *)

val record : Constant.t -> opaque:bool -> unit
(** Log that a non-opaque strategy command named [c] while [c]'s body was an
    opaque proof ([opaque = true]) or not ([opaque = false]). Ignored unless
    logging is enabled. *)

val get : unit -> (Constant.t * bool) list
(** The queries logged so far, newest first, with repeats. *)
