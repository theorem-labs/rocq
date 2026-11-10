Universe u.

Inductive b (A : Type@{u}) := B : A -> b A.

Definition Stmt := forall x : b nat, x = x.
