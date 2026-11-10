Universe u.
#[universes(template=no)]
Inductive b (A : Type@{u}) := B0 : A -> b A.

Theorem thm : forall x : b nat, x = x.
Proof. reflexivity. Qed.
