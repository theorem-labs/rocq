(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val magic_number : int32

type 'a segment = private {
  name : string;
  pos : int64;
  len : int64;
  hash : Digest.t;
}

type 'a id = private { id : string }
(** Private to ensure the phantom tag is injective *)

type in_handle
type out_handle

val make_id : string -> 'a id

val open_in : file:string -> in_handle
val close_in : in_handle -> unit
val marshal_in_segment : in_handle -> segment:'a id -> 'a * Digest.t
val get_segment : in_handle -> segment:'a id -> 'a segment
val segments : in_handle -> Obj.t segment CString.Map.t

val open_out : file:string -> out_handle
val close_out : out_handle -> unit
val marshal_out_segment : out_handle -> segment:'a id -> 'a -> unit
val marshal_out_binary : out_handle -> segment:'a id -> out_channel * (unit -> unit)
(** [marshal_out_binary oh segment] is a low level, stateful, API returning
    [oc, stop]. Once called no other API can be used on the same [oh] and only
    [Stdlib.output_*] APIs should be used on [oc]. [stop ()] must be invoked in
    order to signal that all data was written to [oc] (which should not be used
    afterwards). Only after calling [stop] the other API can be used on [oh]. *)

val append_segment : file:string -> segment:'a id -> 'a -> unit
(** [append_segment ~file ~segment v] adds [v] as a new, additional segment
    to a .vo ALREADY WRITTEN AND CLOSED by [close_out] -- from a process
    other than, and strictly after, the one that wrote it. Does not read,
    re-marshal, or move a single byte of any existing segment: only the
    trailing segment-table and the header's table-pointer are regenerated
    (in a fresh temporary file, atomically renamed over the original, so a
    failure before the rename leaves [file] untouched). Raises an anomaly
    if [file] already has a segment named [segment.id], or if [file] is
    shorter than its own segment table claims. *)
