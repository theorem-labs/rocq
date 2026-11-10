Definition f : Set := nat.

Inductive t := C : f -> t.

Definition Stmt := forall x : t, x = x.
