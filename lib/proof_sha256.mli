(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** SHA-256 (FIPS 180-4), for binding a proof record to the digest the
    grading engine took from the registration's manifest (BET-84 P3). *)

val digest_hex : string -> string
(** The SHA-256 of a string, as 64 lowercase hex digits. *)
