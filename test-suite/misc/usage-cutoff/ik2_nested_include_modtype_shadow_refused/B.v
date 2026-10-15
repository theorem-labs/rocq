Require Import X. Import M. Require Import A.
Module Type Q. Include T. End Q.
Module R : Q. Definition f := 1. End R.
Definition b := R.f.
