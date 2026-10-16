(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Import Ltac2.Std.

(** Abstract type representing a transparency state. *)
Ltac2 Type t.

(** Strategy levels used by [with_strategy].
    [Expand] corresponds to the [-oo] level (always unfold),
    [Opaque] corresponds to the [+oo] level (never unfold),
    and [Level n] corresponds to integer level [n]
    (where [Level 0] is [transparent]). *)
Ltac2 Type strategy_level := [
| Expand
| Opaque
| Level (int)
].

(** [empty] is the empty transparency state (all constants are opaque). *)
Ltac2 @ external empty : t :=
  "rocq-runtime.plugins.ltac2" "empty_transparent_state".

(** [full] is the full transparency state (all constants are transparent). *)
Ltac2 @ external full : t :=
  "rocq-runtime.plugins.ltac2" "full_transparent_state".

(** [current ()] gives the transparency state of the goal, which is influenced
    by, e.g., the [Strategy] command, or the [with_strategy] Ltac tactic. *)
Ltac2 @ external current : unit -> t :=
  "rocq-runtime.plugins.ltac2" "current_transparent_state".

(** [with_strategy lvl refs tac] temporarily sets the strategy level of
    all references in [refs] to [lvl], executes [tac], and then restores
    the original strategy levels. This is the Ltac2 analogue of the
    [with_strategy] Ltac tactic and the [Strategy] vernacular command. *)
Ltac2 @ external with_strategy :
  strategy_level -> Std.reference list -> (unit -> 'a) -> 'a :=
  "rocq-runtime.plugins.ltac2" "with_strategy".
