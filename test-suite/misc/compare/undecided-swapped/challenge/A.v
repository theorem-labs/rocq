(* D is set aside until X and Y map a and b. *)
Unset Elimination Schemes.

Monomorphic Universes a b.

Polymorphic Definition tag@{u} : nat := 0.

Definition D : forall _ : Type@{max(a,b)}, nat := fun _ => tag@{a}.

Inductive X : Type@{a} := cx.
Inductive Y : Type@{b} := cy.

Theorem thm : forall n : nat, n = n.
Proof.
Admitted.
