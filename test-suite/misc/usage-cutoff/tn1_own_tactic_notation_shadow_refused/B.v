Require Import X.
Tactic Notation "tt" := exact 1.
Require Import A.
Definition b0 : nat := ltac:(tt).
Definition b : b0 = 1 := eq_refl.
