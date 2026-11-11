(* The level names exchange roles.  A retry must use the map learned from
   X and Y, not the printed order of a and b. *)
Unset Elimination Schemes.

Monomorphic Universes a b.

Polymorphic Definition tag@{u} : nat := 0.

Definition D : forall _ : Type@{max(a,b)}, nat := fun _ => tag@{b}.

Inductive X : Type@{b} := cx.
Inductive Y : Type@{a} := cy.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.
