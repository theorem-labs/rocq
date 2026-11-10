(* A polymorphic definition is made monomorphic. *)

Inductive colour : Set := Red | Green | Blue.

Definition next (c : colour) : colour :=
  match c with Red => Green | Green => Blue | Blue => Red end.

Definition spare : colour := Blue.

Monomorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.

Lemma given : next Red = Green.
Proof. reflexivity. Qed.

Theorem thm : next (next (next Red)) = Red.
Proof. reflexivity. Qed.
