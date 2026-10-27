(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A canonical, sharing-independent encoding of OCaml values, and SHA-256.

    [coqc] writes, as the digest of a library's [library] segment, the first
    16 bytes of a label computed over the {e value} of that segment and of
    the library's summary with their source locations removed
    ([LibkeyObjects.label]), in place of the MD5 of the segment's bytes.
    [coqc] and [rocqchk] never recompute that digest: they compare the copy
    a dependent recorded with the copy the library's file stores. So a
    dependent stays valid across a rebuild of its dependency that only moves
    source locations. This module gives the encoding that label hashes.

    The encoding is computed in C ([library/rocq_libkey.c]): the walk
    allocates nothing in the OCaml heap, so no collection moves the value
    while it is read, and SHA-256 uses the x86 SHA extensions where the
    processor has them. *)

val version : int
(** Version of the byte layout below. It is part of every label's input, so
    labels made under different layouts never match. Version 2 (label v2,
    design D18 after the Astra review, dispatch://INFRA-361): the encoding
    is version 1's; the version marks labels whose input includes the
    library's summary ([LibkeyObjects]), and {!label} returns the whole
    SHA-256 where version 1 returned its first 16 bytes. *)

exception Unsupported of string
(** The value holds something the layout does not define: a closure, a lazy
    or object block, a custom block (a boxed [Int64], which a 32-bit build
    uses for a primitive integer), or a cycle. *)

val encode : Obj.t -> string
(** The canonical encoding of an OCaml value. It is an encoding of the
    value, not of its marshalled form: two values that differ only in
    physical sharing have the same encoding.

    A value is encoded as [repr v], where [repr v = enc v] when [enc v] is
    shorter than 64 bytes and [repr v = "\007" ^ sha256 (enc v)] otherwise,
    so that one node's encoding stays small whatever its subterms are. With
    [uvar n] the LEB128 of [n >= 0] (seven bits per byte, low bits first,
    the high bit set on every byte but the last) and [f64 x] the 8 bytes of
    the IEEE-754 bits of [x], little-endian, [enc] is:

    - an immediate integer [n]: ["\000"] and [uvar] of its zigzag form
      ([2n] for [n >= 0], [-2n-1] otherwise);
    - a string: ["\001"], [uvar] of its length, and its bytes;
    - a float: ["\002"] and [f64] of it;
    - a flat float array: ["\003"], [uvar] of its length, and [f64] of each
      element;
    - any other block with a tag below [Obj.lazy_tag]: ["\004"], its tag as
      one byte, [uvar] of its size, and [repr] of each field in order;
    - anything else raises {!Unsupported}.

    Every [enc] can be read back field by field, so two values with the same
    encoding are equal, up to a SHA-256 collision.

    Raises [Out_of_memory] when the walk's tables cannot be allocated. *)

val sha256 : string -> string
(** SHA-256 (FIPS 180-4) of a string, as 32 raw bytes. *)

val label : Obj.t -> string
(** [label v]: [sha256] of a header followed by [encode v], 32 bytes. The
    header is the string ["rocq-library-label\000"], then four unsigned
    32-bit little-endian integers: the layout {!version}, the [.vo] format
    version and the word size, then the length of the OCaml version string,
    followed by that string. Raises {!Unsupported} as [encode] does. *)

val stored : string -> string
(** [stored label]: the first 16 bytes of a label, which a [.vo] file stores
    as the digest of its [library] segment (the size of the MD5 digest it
    stands in for). A reader that wants the whole commitment recomputes the
    label from the file's content ([rocq-library-label --check]). *)

(**/**)

val force_portable_sha256 : bool -> unit
(** For the tests: [true] selects the portable SHA-256 even where the x86
    SHA extensions exist, so that both are checked; [false] selects the
    fastest again. *)

val sha256_extensions : unit -> bool
(** For the tests: whether the compression in use is the x86 SHA
    extensions'. *)
