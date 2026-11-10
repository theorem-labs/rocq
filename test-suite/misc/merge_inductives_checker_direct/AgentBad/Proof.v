Require Import Agent.Dup.

Definition weight (s : sev) : nat :=
  match s with
  | SW fd b => fd + b
  | SX code extra => code + extra
  end.

Theorem weight_refl : forall s : sev, weight s = weight s.
Proof. intros s. reflexivity. Qed.
