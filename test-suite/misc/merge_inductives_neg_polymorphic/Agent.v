(* Spec.v's block word for word. *)
Polymorphic Inductive pbox@{u} (A : Type@{u}) := PBox : A -> pbox A.

Theorem thm : forall x : pbox nat, x = x.
Proof. reflexivity. Qed.
