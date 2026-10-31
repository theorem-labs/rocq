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
    read point: the quality graph (row 2), the named context and variable
    opacity (row 3), the typing flags (row 4), every option and the warning
    flags (row 13), the generalizable identifiers (M3) and the template
    default levels (M7). It also starts the proof's universe footprint: the
    levels every universe-graph operation names until the proof ends. A no-op
    when no proof is recorded. *)

val record_universe_footprint : unit -> unit
(** Records row 2 for the open proof: the order the start-of-proof global
    graph induces on the footprint's global levels, or the whole graph's
    digest. Call it while the proof is still recorded, before [Qed]'s
    declaration. *)

val drop_universe_frame : unit -> unit
(** Ends the footprint of the innermost proof the recorder holds (its [Qed],
    [Admitted] or [Abort]). *)

val drop_universe_frames : unit -> unit
(** Ends every footprint ([Abort All], a reset). *)

type declaration_queries = {
  dq_levels : Univ.Level.Set.t;  (** every level a query named *)
  dq_whole : bool;  (** some query read a whole graph *)
}

val with_declaration_queries : (unit -> 'a) -> 'a * declaration_queries
(** Runs a declaration and collects the universe-graph queries it makes
    outside the kernel ({!Global.in_kernel}): the ones that a proof's own
    universe state answers. The footprint goes on being taken beside it. *)

val universe_state_view : levels:Univ.Level.t list -> UState.t -> string
(** A digest of what the two graphs of a universe state answer about these
    levels: whether each graph checks universes, its quality variables
    above [Prop], which of the levels it declares, and the order it proves
    between each pair of the declared ones. *)

val universe_graph_value : UGraph.t -> string
(** The digest of a whole graph, the one the footprint records when it
    reads the whole graph. *)

type universe_footprint

val universe_footprint_of_key : string -> universe_footprint option

val universe_footprint_value : UGraph.t -> universe_footprint -> string
(** The row 2 value of a footprint against a global graph, for the recorder
    and for {!Proof_replay_env}. *)

val start_reads : unit -> Proof_record.read list
(** The same reads as values, for the side that checks them again:
    {!Proof_replay_env} evaluates this list at the proof it is about to
    replay, so the recorded value and the value now are made the same
    way. *)
