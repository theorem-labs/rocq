Ltac t := constructor.

Lemma lpar : True /\ True.
Proof. split. par: t. Qed.

Lemma lall : True /\ True.
Proof. split. all: t. Qed.
