(* The control: a nested proof's closer is not a drop. After each closer
   below (Qed in a focused block, Admitted, Defined, Proof term, Qed), the
   proof stack holds outer again. Each later inner proof is nested too and
   is not counted. *)
Set Nested Proofs Allowed.

Lemma outer : True.
Proof.
  assert (H : True).
  { Lemma inner_qed : True.
    Proof. exact I. Qed.
    exact inner_qed. }
  Lemma inner_admitted : True.
  Admitted.
  Lemma inner_defined : True.
  Proof. exact I. Defined.
  Lemma inner_term : True.
  Proof I.
  Lemma inner_last : True.
  Proof. exact I. Qed.
  exact I.
Qed.

Lemma after_nested : True.
Proof. exact I. Qed.
