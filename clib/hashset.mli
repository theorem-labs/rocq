(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Adapted from Damien Doligez, projet Para, INRIA Rocquencourt,
    OCaml stdlib. *)

(** The following functor is a specialized version of [Weak.Make].
    Here, the responsibility of computing the hash function is now
    given to the caller, which makes possible the interleaving of the
    hash key computation and the hash-consing. *)

module type EqType = sig
  type t
  val eq : t -> t -> bool
end

type statistics = {
  num_bindings: int;
  num_buckets: int;
  max_bucket_length: int;
  bucket_histogram: int array
}

val retain_entries : unit -> unit
(** From this call on, each hashset keeps every element it stores alive for as
    long as the set itself, instead of holding it weakly. The call first runs a
    full major collection and then keeps every element still in a set made
    before it, so the elements that module initialisers stored are kept too,
    exactly those reachable at the call.

    A weak set forgets an element only when the garbage collector reclaims it,
    and until then [repr] still returns it, even when nothing else holds it. So
    whether a value built later is shared with an earlier, dead one depends on
    when collections happen, which depends on everything the process allocated
    before (its arguments and environment, the directories it reads, the GC
    parameters). That sharing is what [Marshal] records, so a compiled file's
    bytes, and the digest its dependents check, could change with any of these.
    With the elements kept, [repr]'s answers depend only on the sequence of
    calls, so the same source and arguments compile to the same bytes.

    The cost is memory: an element that dies early is kept until the process
    ends. A compilation process, which ends with its file, calls this; an
    interactive process does not. *)

module type S = sig
  type elt
  (** Type of hashsets elements. *)

  type t
  (** Type of hashsets. *)

  val create : int -> t
  (** [create n] creates a fresh hashset with initial size [n]. *)

  val clear : t -> unit
  (** Clear the contents of a hashset. *)

  val repr : int -> elt -> t -> elt
  (** [repr key constr set] uses [key] to look for [constr]
      in the hashet [set]. If [constr] is in [set], returns the
      specific representation that is stored in [set]. Otherwise,
      [constr] is stored in [set] and will be used as the canonical
      representation of this value in the future. *)

  val stats : t -> statistics
  (** Recover statistics on the table. *)
end

module Make (E : EqType) : S with type elt = E.t

module Combine : sig
  val combine : int -> int -> int
  val combinesmall : int -> int -> int
  val combine3 : int -> int -> int -> int
  val combine4 : int -> int -> int -> int -> int
  val combine5 : int -> int -> int -> int -> int -> int
end
