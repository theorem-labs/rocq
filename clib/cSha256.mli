(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** SHA-256 (FIPS 180-4), in OCaml. The standard library's {!Digest} is MD5,
    and a consumer that names a file by the hash of its bytes needs a hash
    that two different files do not share. *)

val string : string -> string
(** The digest of a string, as 64 lowercase hexadecimal characters. *)

val file : string -> string
(** The digest of the bytes of a file, as 64 lowercase hexadecimal
    characters. Raises [Sys_error] when the file cannot be read. *)
