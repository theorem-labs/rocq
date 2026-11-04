Declare ML Module "coq-test-suite.bad_name".

Module Type T. Parameter x : Set. End T.

(* A functor sealed by T: its implementation has a field that T has not. *)
Module F (X : T) : T.
  Definition x : Set := nat.
  Test Line Break Axiom zqxbad zqxforged.
End F.
