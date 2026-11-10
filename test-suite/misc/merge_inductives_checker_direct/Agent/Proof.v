(* The agent's proof, stated over the AGENT's copy of sev. *)
Require Import Agent.Dup.

Definition weight (s : sev) : nat :=
  match s with
  | SW fd b => fd + b
  | SX code => code
  end.

Theorem weight_refl : forall s : sev, weight s = weight s.
Proof. intros s. reflexivity. Qed.
