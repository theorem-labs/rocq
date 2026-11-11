Inductive wrap (A : Type) := Wrap : A -> wrap A.

Definition size (w : wrap nat) : nat := match w with Wrap _ a => S a end.

Definition Stmt := forall w : wrap nat, size w >= 1.
