Axiom base_ax : True.
Definition base_def := 3.
Lemma base_lemma : base_def = 3. Proof. reflexivity. Qed.
Inductive tree := Leaf | Node (f : forest)
with forest := Nil | Cons (t : tree) (f : forest).
Lemma uses_ax : True. Proof. exact base_ax. Qed.
Module Type T. Parameter p : nat. End T.
Module F (X : T). Lemma fl : X.p = X.p. Proof. reflexivity. Qed. End F.
