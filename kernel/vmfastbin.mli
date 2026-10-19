(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** C fast paths for [Pos.compare_cont] and [Pos.eqb] in the VM interpreter.

    The fast path is on unless the environment sets [ROCQ_VM_FASTBIN=0]. *)

(** Called for every constant the checker checks. Records [body] as the
    reference for a fast path only when [kn] is the canonical Corelib
    constant and the body's serialization equals the one pinned in this
    module. *)
val capture_reference :
  Names.Constant.t -> (Constr.t, 'opaque, 'rules) Declarations.constant_def -> unit

(** Called when the VM links a constant's closure. Registers [value] with the
    interpreter when the constant is monomorphic and [body] is
    [Constr.equal] to a recorded reference. *)
val register : Declarations.universes -> Constr.t -> Vmvalues.values -> unit
