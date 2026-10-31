Create HintDb mydb.

Lemma h1 : True.
Proof. exact I. Qed.

Lemma h2 : 0 = 0.
Proof. reflexivity. Qed.

#[local] Hint Resolve h1 : mydb.

Lemma uses_db : True.
Proof. auto with mydb. Qed.
