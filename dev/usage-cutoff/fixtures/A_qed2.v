Require Import X.
Lemma a : forall n : nat, n + 0 = n.
Proof.
  intros n; induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.
