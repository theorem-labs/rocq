Lemma early : 1 = 1.
Proof. reflexivity. Qed.

Definition changed := 1 + 1.

Lemma reads_changed : changed = 2.
Proof. unfold changed. reflexivity. Qed.
