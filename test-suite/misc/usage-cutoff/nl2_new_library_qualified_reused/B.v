Require Import X A.
Definition b : X.f0 = 1 := eq_refl.
Import X.
Definition b2 : f0 = 1 := eq_refl.
