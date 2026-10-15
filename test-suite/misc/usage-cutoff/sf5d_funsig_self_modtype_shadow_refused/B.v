Require Import X A.
Module Type FT (P : S). Module Type T. Parameter f : nat. End T. Module Q. Include T. End Q. Parameter h : Q.f = Q.f. End FT.
Definition b := 0.
