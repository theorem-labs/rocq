(* The statement gains a hypothesis. *)
Require Import Pre.Shared.

Definition Agent := Type.

Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.

Theorem thm : forall n : nat, n = 0 -> n = n.
Proof. reflexivity. Qed.

Theorem other : forall b : bool, b = b.
Proof. reflexivity. Qed.
