(* thm is given the statement of the other theorem. *)
Require Import Pre.Shared.

Definition Agent := Type.

Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.

Theorem thm : forall b : bool, b = b.
Proof. reflexivity. Qed.

Theorem other : forall b : bool, b = b.
Proof. reflexivity. Qed.
