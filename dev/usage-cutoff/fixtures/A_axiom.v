Require Import X.
Lemma a : forall n : nat, n + 0 = n.
Proof. pose proof (classic True) as _H. clear _H. induction n; simpl; auto. Qed.
