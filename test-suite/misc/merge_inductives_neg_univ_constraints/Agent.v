(* Spec.v's block with one constraint more in the block's own universe
   context. *)

#[universes(polymorphic)]
Inductive b@{u v | u <= v} (A1 : Type@{u}) (A2 : Type@{v}) := Mk : A1 -> A2 -> b A1 A2.

Theorem thm : forall x : b@{Set Set} nat nat, x = x.
Proof. reflexivity. Qed.
