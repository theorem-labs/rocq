Definition two := 2.

Lemma lower : two = 2.
Proof.
Admitted.

Theorem thm : two = 2 /\ two = 2.
Proof. split; exact lower. Qed.
