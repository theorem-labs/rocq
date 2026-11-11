(* With all three inductives absent, no retry pass can map either level of D. *)
Unset Elimination Schemes.

Monomorphic Universes a b c.

Polymorphic Definition tag@{u} : nat := 0.

Definition D : forall _ : Type@{max(a,b)}, nat := fun _ => tag@{a}.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.