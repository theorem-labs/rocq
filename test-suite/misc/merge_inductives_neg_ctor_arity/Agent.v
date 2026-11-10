(* Spec.v's block, with one argument more on the constructor. *)

Inductive t := C : nat -> nat -> t.

Theorem thm : forall x : t, x = x.
Proof. reflexivity. Qed.
