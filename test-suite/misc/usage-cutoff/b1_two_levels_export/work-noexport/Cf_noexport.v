Require Import Bf_noexport.
Definition bad : 2 = 1 := b.
Lemma f : False.
Proof. discriminate bad. Qed.
Print Assumptions f.
