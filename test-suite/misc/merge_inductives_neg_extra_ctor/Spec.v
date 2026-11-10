Inductive color := Red | Green.

Definition Stmt := forall c : color, c = c.

(* Spec's own view of its type: there are two colours and no more. *)
Lemma all : forall c : color, c = Red \/ c = Green.
Proof. destruct c; [left | right]; reflexivity. Qed.
