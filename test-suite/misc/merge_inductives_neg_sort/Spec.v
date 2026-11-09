Inductive p : Prop := P0 : p | P1 : p.

Definition Stmt := forall x : p, x = x.
