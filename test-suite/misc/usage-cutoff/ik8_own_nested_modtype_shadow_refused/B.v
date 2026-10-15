Require Import X A.
Module M. Module Type T. Parameter f : nat. End T. End M.
Import M.
Module Q. Include T. End Q.
Definition b := Q.f.
