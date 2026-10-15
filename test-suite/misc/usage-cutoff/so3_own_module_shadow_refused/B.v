Require Import X.
Module N. Definition f := 1. End N.
Require Import A.
Import N.
Definition b : f = 1 := eq_refl.
