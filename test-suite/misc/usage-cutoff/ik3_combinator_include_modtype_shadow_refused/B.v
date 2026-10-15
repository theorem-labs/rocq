Require Import X A.
Module Type Q := T0 <+ T.
Module R : Q. Definition f := 1. End R.
Definition b := R.f.
