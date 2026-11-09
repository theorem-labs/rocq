(* Spec.v's block word for word. *)
#[universes(template)]
Inductive tbox (A : Type) := TBox : A -> tbox A.

Theorem thm : forall x : tbox nat, x = x.
Proof. reflexivity. Qed.
