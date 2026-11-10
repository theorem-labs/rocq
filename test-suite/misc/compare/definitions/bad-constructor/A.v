(* An inductive type gains a constructor. *)

Inductive colour : Set := Red | Green | Blue | White.

Definition next (c : colour) : colour :=
  match c with Red => Green | Green => Blue | Blue => Red | White => Red end.

Definition spare : colour := Blue.

Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.

Lemma given : next Red = Green.
Proof. reflexivity. Qed.

Theorem thm : next (next (next Red)) = Red.
Proof. reflexivity. Qed.
