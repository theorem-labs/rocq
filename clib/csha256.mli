(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** binary-equivalence-taiga#841: a from-scratch SHA-256 (FIPS 180-4), used
    for this fork's reuse-decision digests computed over agent-controlled
    bytes (MD5/[Digest.t] remains, unchanged, for the stock whole-library
    [vodigest] -- see the implementation's doc comment for why). *)

type t = string
(** A 32-byte binary digest -- same convention as [Digest.t]'s opaque
    fixed-length [string] (16 bytes there, 32 here). *)

val digest : string -> t
val equal : t -> t -> bool
val to_hex : t -> string
