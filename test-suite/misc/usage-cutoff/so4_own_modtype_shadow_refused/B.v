Require Import X.
Module Type T. Parameter f : nat. End T.
Require Import A.
Module R : T. Definition f := 1. End R.
Definition b := R.f.
