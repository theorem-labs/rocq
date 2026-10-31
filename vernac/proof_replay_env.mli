(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** What a recorded read is worth now (BET-84, part P3). *)

val init : unit -> unit
(** Registers this layer's read evaluators with {!Proof_replay}. Call it
    once, before the compile. A channel with no evaluator here makes every
    proof that read it miss, which the compile's summary counts by
    channel. *)
