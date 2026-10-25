Axiom bad : True.

Lemma helper : True.
Proof. exact bad. Qed.

Lemma later : True.
Proof. exact helper. Qed.

Print Assumptions later.
