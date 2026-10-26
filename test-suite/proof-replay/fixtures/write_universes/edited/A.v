Lemma writer : forall A : Type, A -> A.
Proof. intros A x. exact x. Qed.

Lemma changed_reader : forall A : Type, A -> A.
Proof. intros A x. refine x. Qed.

Lemma later_reader : forall A : Type, A -> A.
Proof. intros A x. exact x. Qed.
