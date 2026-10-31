Lemma hint_source : True.
Proof. exact I. Qed.

Lemma writer : True.
Proof. auto using hint_source. Qed.

#[local] Hint Resolve writer.

Lemma later_reader : True.
Proof. auto. Qed.
