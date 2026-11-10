(* A transparent challenge definition is made opaque. Nothing else changes,
   and no proof needs to compute with it, so opacity is the only
   difference. *)

Inductive colour : Set := Red | Green | Blue.

Definition next (c : colour) : colour :=
  match c with Red => Green | Green => Blue | Blue => Red end.

Definition spare : colour.
Proof. exact Blue. Qed.

Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.

Lemma given : next Red = Green.
Proof. reflexivity. Qed.

Theorem thm : next (next (next Red)) = Red.
Proof. reflexivity. Qed.
