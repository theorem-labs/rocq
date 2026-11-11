(* X maps the challenge's a to this answer's b and Z maps its c to this
   answer's a.  With Y missing, D can only map the challenge's b to an
   answer level already used by c. *)
Unset Elimination Schemes.

Monomorphic Universes a b c.

Polymorphic Definition tag@{u} : nat := 0.

Definition D : forall _ : Type@{max(a,b)}, nat := fun _ => tag@{a}.

Inductive X : Type@{b} := cx.
Inductive Z : Type@{a} := cz.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.
