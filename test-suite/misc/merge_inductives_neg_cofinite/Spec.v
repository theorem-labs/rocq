(* No base case: nothing inhabits this type. *)
Inductive stream := Cons : nat -> stream -> stream.

Definition Stmt := forall x : stream, x = x.

Lemma empty : stream -> False.
Proof. intro x. induction x as [n s IH]. exact IH. Qed.
