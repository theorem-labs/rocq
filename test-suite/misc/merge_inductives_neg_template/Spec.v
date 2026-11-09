#[universes(template)]
Inductive w (A : Type) := W : A -> w A.

Definition Stmt := forall x : w nat, x = x.
