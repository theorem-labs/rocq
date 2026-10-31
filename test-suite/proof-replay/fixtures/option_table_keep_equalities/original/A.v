(* injection keeps an equality between two proofs of a Prop inductive only
   when the inductive is in the Keep Equalities table, a Goptions table that
   Add and Remove change (Equality.keep_head_inductive). The edited tree
   removes the Add, so stock injection finds no equality to keep and fails;
   the proof's sentences, its statement and its other reads are unchanged.
   Replay must fail too (cross-family review of 079bc4cb71, finding CF1,
   trigger T1). *)
Inductive bar : Prop := bar_1.
Add Keep Equalities bar.

Lemma p : forall a b : bar, Some a = Some b -> a = b.
Proof.
  intros a b H.
  injection H as E.
  exact E.
Qed.
