Universe u.
Universe v.
#[universes(template=no)]
Inductive b (A : Type@{u}) (B : Type@{v}) := B0 : A -> B -> b A B.

Theorem thm : forall x : b nat bool, x = x.
Proof. reflexivity. Qed.
