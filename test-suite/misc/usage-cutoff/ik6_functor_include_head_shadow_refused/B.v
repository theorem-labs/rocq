Require Import X A.
Module Type Q. Include FT E. End Q.
Module R : Q. Definition f := 1. End R.
Definition b := R.f.
