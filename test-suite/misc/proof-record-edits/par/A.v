Ltac t := exact I.

Lemma lpar : True /\ True.
Proof. split. par: t. Qed.

Lemma lall : True /\ True.
Proof. split. all: t. Qed.
