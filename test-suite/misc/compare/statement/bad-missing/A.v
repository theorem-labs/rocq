(* The answer does not hold thm at all. *)
Require Import Pre.Shared.

Definition Agent := Type.

Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.

Theorem other : forall b : bool, b = b.
Proof. reflexivity. Qed.
