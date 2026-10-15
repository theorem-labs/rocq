Require Import Bf_export.
Definition bad : 2 = 1 := b.
Lemma f : False.
Proof. discriminate bad. Qed.
Print Assumptions f.
