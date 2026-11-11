Inductive color := Red | Green.

Inductive tree := Leaf : color -> tree | Node : tree -> tree -> tree.

Fixpoint size (t : tree) : nat :=
  match t with Leaf _ => 1 | Node a b => size a + size b end.

Definition Stmt := forall t : tree, size t >= 1.
