Inductive t := C : nat -> t.

Definition Stmt := forall x : t, x = x.
