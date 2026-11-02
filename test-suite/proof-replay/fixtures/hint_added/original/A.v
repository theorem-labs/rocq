Create HintDb mydb.

Lemma base : True.
Proof. exact I. Qed.

Lemma other : True /\ True.
Proof. split; exact I. Qed.

#[local] Hint Resolve base : mydb.

Lemma uses_db : True.
Proof. auto with mydb. Qed.

Lemma no_db : 1 = 1.
Proof. reflexivity. Qed.
