Require Import X B.
Lemma bad : False.
Proof.
  assert (H2 : X.foo = 2) by reflexivity.
  rewrite b in H2.
  discriminate.
Qed.
