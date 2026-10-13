Require Import X.
Lemma helper : True.
Proof. exact I. Qed.
Lemma a : forall n : nat, n + 0 = n.
Proof. induction n; simpl; auto. Qed.
