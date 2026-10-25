Set Nested Proofs Allowed.

Lemma outer : True.
Proof.
  assert (H : True).
  { Lemma inner : True.
    Proof. exact I. Qed.
    exact inner. }
  exact I.
Qed.
