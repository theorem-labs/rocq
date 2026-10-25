Create HintDb db.

Lemma main_hint : True.
Proof. exact I. Qed.

Lemma unused_hint : 0 = 0.
Proof. reflexivity. Qed.

#[local] Hint Resolve main_hint unused_hint : db.

Lemma reads_db : True.
Proof. auto with db. Qed.
