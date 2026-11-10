Definition two := 2.

Lemma given : two = 2.
Proof. reflexivity. Qed.

Theorem thm : two = 2.
Proof. exact given. Qed.
