Require Import X.
Lemma a : forall n : nat, n + 0 = n.
Proof. induction n; simpl; auto. Qed.
