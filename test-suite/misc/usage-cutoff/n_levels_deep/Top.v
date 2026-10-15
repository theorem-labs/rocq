Require Import L5.
Definition bad : 2 = 1 := b.
Lemma contradiction : False.
Proof. discriminate bad. Qed.
Print Assumptions contradiction.
