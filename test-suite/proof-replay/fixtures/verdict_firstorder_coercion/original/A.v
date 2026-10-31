(* firstorder unfolds every constant except the coercions: it reads the whole
   coercion table to build its reduction flags. The edited tree declares W a
   coercion, so firstorder no longer sees the disjunction inside [W n], leaves
   the goal open, and the stock script fails at Qed. Replay must fail too: the
   coercion table is the only input that changed (gate review, breadth audit
   gap BA3). The solver is given: a plain [firstorder] reads its default
   solver, a tactic option with no evaluator, so it never replays. *)
Definition W (n : nat) : Prop := n = 0 \/ n = 1.

Lemma p : forall n, W n -> n = 1 \/ n = 0.
Proof. firstorder auto. Qed.
