Polymorphic Inductive pbox@{u} (A : Type@{u}) := PBox : A -> pbox A.

Definition Stmt := forall x : pbox nat, x = x.
