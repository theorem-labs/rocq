#[deprecated(since="0.1")]
Definition old := 0.

Lemma writer : True.
Proof. pose proof (eq_refl old) as H. exact I. Qed.

Lemma later_reader : True.
Proof. exact writer. Qed.
