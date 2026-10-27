Declare ML Module "coq-test-suite.bad_name".

Module Type T. Parameter x : Set. End T.

(* The field is in the body of a functor module type, which only its
   signature holds. *)
Module Type FT (X : T).
  Test Line Break Axiom zqxbad zqxforged.
End FT.
