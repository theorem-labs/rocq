#[universes(template)]
Inductive tbox (A : Type) := TBox : A -> tbox A.

Definition Stmt := forall x : tbox nat, x = x.
