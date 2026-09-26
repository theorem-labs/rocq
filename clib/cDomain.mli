(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The subset of OCaml 5's [Domain] used by Rocq, with a single-domain
    fallback on OCaml 4. *)

val available : bool
(** [false] on OCaml 4, where {!spawn} and {!join} must not be called. *)

type 'a t
val spawn : (unit -> 'a) -> 'a t
val join : 'a t -> 'a

val self_index : unit -> int
(** The index of the current domain; always [0] on OCaml 4. *)

module DLS : sig
  type 'a key
  val new_key : (unit -> 'a) -> 'a key
  val get : 'a key -> 'a
  val set : 'a key -> 'a -> unit
end
