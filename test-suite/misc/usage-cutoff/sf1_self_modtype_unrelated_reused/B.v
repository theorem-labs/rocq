Require Import X A.
Module Type T. Parameter f : nat. End T.
Module Type Q. Include T. End Q.
Module R : Q. Definition f := 1. End R.
Definition b := R.f.
