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
open Vmemitcodes

type t
(** Type of VM libraries. *)

type index

type indirect_code = index pbody_code

type compiled_library
type on_disk

val segment_name : string
(** Name of the .vo segment this module writes and reads. *)

val format_version : int
(** Format version of that segment, the 32-bit big-endian word it starts with.
    [load] refuses a segment carrying any other value, and a reader that does not
    go through [load] (checker/votour.ml) names the version it reads. *)

val empty : t

val set_path : DirPath.t -> t -> t

val add : to_patch -> t -> t * index

val save : ObjFile.out_handle -> compiled_library -> unit
(** Writes the segment: its format version, then the table. *)

val load : DirPath.t -> file:string -> ObjFile.in_handle -> on_disk
(** Reads the segment's format version and refuses a library that does not carry
    [format_version]. The table itself is read on demand. *)

val link : on_disk -> t -> t

val inject : compiled_library -> on_disk

val resolve : index -> t -> to_patch

val export : t -> compiled_library
