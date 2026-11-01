Declare ML Module "coq-test-suite.bad_name".

Module Type T. Parameter x : Set. End T.

(* The field is in a module type U of the implementation of M, which T has
   not. *)
Module M : T.
  Definition x : Set := nat.
  Module Type U.
    Test Line Break Axiom zqxbad zqxforged.
  End U.
End M.
