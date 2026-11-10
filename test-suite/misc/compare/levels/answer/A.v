Monomorphic Definition f@{i j} (X : Type@{i}) : Type@{j} := X.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.
