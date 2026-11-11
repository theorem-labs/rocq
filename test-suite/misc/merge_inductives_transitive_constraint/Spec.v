Universe u.
Constraint Set < u.
#[universes(template=no)]
Inductive b (A : Type@{u}) := B0 : A -> b A.

Definition Stmt := forall x : b nat, x = x.
