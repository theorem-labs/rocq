(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a const_entry_body = 'a Entries.proof_output Future.computation

(** When set, {!declare_defined_opaque} does not let the kernel check the
    proof, and records it as not checked, unless the proof is declared under
    {!with_qed_typecheck_forced}. Default [false]. The
    [-skip-qed-typecheck] option sets it. The [Skip Qed Typecheck] flag has
    the same effect on each proof declared while it is on. *)
val skip_qed_typecheck : bool ref

(** [with_qed_typecheck_forced f] runs [f] with the kernel's check of a Qed
    proof forced on, whatever {!skip_qed_typecheck} and the [Skip Qed
    Typecheck] flag say. A command control that observes the error or the
    result of the command it wraps and then discards its effect ([Fail],
    [Succeed]) runs the command under it: the skip would otherwise turn the
    error [Qed] raises on an ill-typed proof into a success, which changes
    the verdict of the enclosing control, and the proof it discards reaches
    no [.vo] for [rocqchk] to check. *)
val with_qed_typecheck_forced : (unit -> 'a) -> 'a

val declare_defined_opaque : ?feedback_id:Stateid.t -> poly:bool ->
  Opaqueproof.opaque_handle -> Safe_typing.private_constants const_entry_body -> unit
val declare_private_opaque : Safe_typing.exported_opaque -> unit

(** A table of opaque proofs. Each entry also records whether the kernel did
    not check the proof, see {!skip_qed_typecheck}. *)
type opaque_disk

val get_opaque_disk : Opaqueproof.opaque_handle -> opaque_disk -> (Opaqueproof.opaque_proofterm * bool) option
val set_opaque_disk : Opaqueproof.opaque_handle -> Opaqueproof.opaque_proofterm -> opaque_disk -> unit

val get_current_opaque : Opaqueproof.opaque_handle -> (Opaqueproof.opaque_proofterm * bool) option
val get_current_constraints : Opaqueproof.opaque_handle -> Univ.ContextSet.t option

val dump : ?except:Future.UUIDSet.t -> unit -> opaque_disk * Opaqueproof.opaque_handle Future.UUIDMap.t

module Summary :
sig
  type t
  val init : unit -> unit
  val freeze : unit -> t
  val unfreeze : t -> unit
  val join : ?except:Future.UUIDSet.t -> unit -> unit
end
