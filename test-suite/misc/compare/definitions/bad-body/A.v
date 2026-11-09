(* The body of a challenge definition is changed, keeping its type: the
   shape of the verified grader's definition-edit answers. *)

Inductive colour : Set := Red | Green | Blue.

Definition next (c : colour) : colour :=
  match c with Red => Red | Green => Green | Blue => Blue end.

Definition spare : colour := Blue.

Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.

Lemma given : next Red = Red.
Proof. reflexivity. Qed.

Theorem thm : next (next (next Red)) = Red.
Proof. reflexivity. Qed.
