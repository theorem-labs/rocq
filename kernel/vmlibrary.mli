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

val vm_segment : compiled_library ObjFile.id

val empty : t

val set_path : DirPath.t -> t -> t

val add : to_patch -> t -> t * index

val load : DirPath.t -> file:string -> ObjFile.in_handle -> on_disk

val of_thunk : DirPath.t -> (unit -> to_patch array) -> on_disk
(** [of_thunk dp f] is the code table of library [dp], computed by [f] the first
    time one of its indices is resolved, and memoised afterwards. Used by the
    checker, which recompiles the bytecode of a library on demand rather than
    reading it from the file. The [i]-th element of the array is the code of
    [foreign_index dp i]. *)

val foreign_index : DirPath.t -> int -> index
(** The index of the [i]-th slot of the library [dp]. Only makes sense for a
    library linked with [link], never for the local table. *)

val link : on_disk -> t -> t

val inject : compiled_library -> on_disk

val resolve : index -> t -> to_patch

val export : t -> compiled_library
