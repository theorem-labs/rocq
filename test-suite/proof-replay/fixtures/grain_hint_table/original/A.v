Create HintDb db.

Lemma main_hint : True.
Proof. exact I. Qed.

#[local] Hint Resolve main_hint : db.

Lemma reads_db : True.
Proof. auto with db. Qed.
