Require Import B.
Definition bad : 2 = 1 := b.
Lemma contradiction : False.
Proof. discriminate bad. Qed.
Print Assumptions contradiction.
