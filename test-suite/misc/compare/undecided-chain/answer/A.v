Unset Elimination Schemes.

Monomorphic Universes a b c d.

Definition P : Type@{max(a,b)} -> nat := fun _ => 0.
Definition Q : Type@{max(b,c)} -> nat := fun _ => 0.
Definition R : Type@{max(c,d)} -> nat := fun _ => 0.

Inductive X : Type@{d} := cx.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.
