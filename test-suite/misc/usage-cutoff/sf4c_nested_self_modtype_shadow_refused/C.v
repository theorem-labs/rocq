Require Import B.
Module R : U. Module Type T. Parameter f : nat. End T. Definition f := 1. End R.
Check R.f.
