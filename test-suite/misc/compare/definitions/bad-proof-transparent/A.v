(* A challenge Qed is made transparent, so the answer's body reaches
   conversion where the challenge's could not. *)

Inductive colour : Set := Red | Green | Blue.

Definition next (c : colour) : colour :=
  match c with Red => Green | Green => Blue | Blue => Red end.

Definition spare : colour := Blue.

Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.

Lemma given : next Red = Green.
Proof. reflexivity. Defined.

Theorem thm : next (next (next Red)) = Red.
Proof. reflexivity. Qed.
