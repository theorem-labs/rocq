(* D's type is deferred before X, Y and Z map a, b and c.  Its body is
   reached only on retry, where tag@{b} conflicts with tag@{a}'s mapping. *)
Unset Elimination Schemes.

Monomorphic Universes a b c.

Polymorphic Definition tag@{u} : nat := 0.

Definition D : forall _ : Type@{max(a,b)}, nat := fun _ => tag@{b}.

Inductive X : Type@{a} := cx.
Inductive Y : Type@{b} := cy.
Inductive Z : Type@{c} := cz.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.