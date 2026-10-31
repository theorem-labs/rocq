(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [rocq proof-record-inline RECORD VO OUT] (BET-84): write to [OUT] the
    proof record [RECORD] with every term that refers to the opaque proofs
    of the object [VO] put back inline ({!Declare.inline_proof_record}).
    It runs in the worker that replays the record, so the stored terms are
    read and written by the binary that reads them back. On an error it
    prints why, writes nothing and exits 1; on a usage error it exits 2. *)

val main : string list -> unit
