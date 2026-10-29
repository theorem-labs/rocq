Create Rewrite HintDb db.
Lemma labsent : bool.
Proof. tryif autorewrite with db then exact true else exact false. Qed.
