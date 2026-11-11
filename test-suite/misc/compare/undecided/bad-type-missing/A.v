(* D is deferred.  After the inductives map a, b and c, its retry cannot
   match the challenge's mapped b against the answer universe max(a,c). *)
Unset Elimination Schemes.

Monomorphic Universes a b c.

Polymorphic Definition tag@{u} : nat := 0.

Definition D : forall _ : Type@{max(a,c)}, nat := fun _ => tag@{a}.

Inductive X : Type@{a} := cx.
Inductive Y : Type@{b} := cy.
Inductive Z : Type@{c} := cz.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.
