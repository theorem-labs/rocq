(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** What {!Proof_recorder} needs from the vernac layer (BET-84, part P2). *)

val toolchain : unit -> Proof_record.toolchain
(** Key item 2, read now: the running binary, every loaded plugin and
    library in load order with their digests, the [-w] flags, the
    safe-loaded libraries, and the stack limit. *)

val position : unit -> Proof_record.position
(** Key item 3: the current module path and section prefix ([Lib] state).
    [module_path] is the path the [.glob] file writes for a definition
    (sections excluded); [section_path] adds the open sections. *)

val read_at_start : unit -> unit
(** Records, as reads of the open proof, the channels that have no single
    read point: the universe and quality graphs (row 2), the named context
    and variable opacity (row 3), the typing flags (row 4), every option
    and the warning flags (row 13), the generalizable identifiers (M3) and
    the template default levels (M7). A no-op when no proof is open. *)

val start_reads : unit -> Proof_record.read list
(** The same reads as values, for the side that checks them again:
    {!Proof_replay_env} evaluates this list at the proof it is about to
    replay, so the recorded value and the value now are made the same
    way. *)
