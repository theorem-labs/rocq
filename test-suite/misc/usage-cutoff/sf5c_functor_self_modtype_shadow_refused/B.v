Require Import X A.
Module F (P : S). Module Type T. Parameter f : nat. End T. Module Q. Include T. End Q. Definition h := Q.f. End F.
Definition b := 0.
