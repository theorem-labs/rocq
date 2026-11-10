(* Spec.v's two types, word for word, in two blocks of one instead of one
   block of two. *)

Inductive even := E0 : even | ES : even -> even.

Inductive odd := OS : odd -> odd.

Theorem thm : forall x : even, x = x.
Proof. reflexivity. Qed.
