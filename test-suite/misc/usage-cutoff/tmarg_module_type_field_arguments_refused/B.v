Require Import X A.
Module M : T. Definition f (x : nat) := x. End M.
Definition b := M.f 1.
