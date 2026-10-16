Require Import X.
Ltac t := exact 1.
Require Import A.
Definition b0 : nat := ltac:(t).
Definition b : b0 = 1 := eq_refl.
