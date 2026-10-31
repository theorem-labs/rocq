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
val input_segment_int : in_handle -> segment:'a id -> int
(** Reads the 32-bit big-endian integer a segment's data starts with, without
    unmarshalling anything. Only for a segment whose own format begins with one
    (today: the vmlibrary segment's format version, kernel/vmlibrary.ml). *)
val segments : in_handle -> Obj.t segment CString.Map.t

val open_out : file:string -> out_handle
val close_out : out_handle -> unit
val marshal_out_segment : ?hash:Digest.t -> out_handle -> segment:'a id -> 'a -> unit
(** [marshal_out_segment ~hash oh ~segment v] writes [v] as [segment] and
    stores [hash] as its digest, in the segment table and after the data.
    Without [hash], the digest is the MD5 of the bytes written. The readers
    in this module only compare the two stored copies and recompute no
    digest. Readers above it hash a segment themselves, each for its own
    question: rocq-library-label hashes the [keepfacts] segment and reads it
    as absent unless the digest matches, and hashes the [library] segment to
    say whether its digest is that MD5 or something else
    (checker/library_label.ml); coqc hashes the [library] segment for the
    same question ([Library.label_digested]). *)
val marshal_out_binary : out_handle -> segment:'a id -> out_channel * (unit -> unit)
(** [marshal_out_binary oh segment] is a low level, stateful, API returning
    [oc, stop]. Once called no other API can be used on the same [oh] and only
    [Stdlib.output_*] APIs should be used on [oc]. [stop ()] must be invoked in
    order to signal that all data was written to [oc] (which should not be used
    afterwards). Only after calling [stop] the other API can be used on [oh]. *)
