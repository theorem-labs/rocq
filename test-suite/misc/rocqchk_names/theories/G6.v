Declare ML Module "coq-test-suite.bad_name".

Module Type T. Parameter x : Set. End T.

(* F is not sealed, so its fields are only in its signature, the body of a
   functor. *)
Module F (X : T).
  Definition x : Set := nat.
  Test Line Break Axiom zqxbad zqxforged.
End F.
