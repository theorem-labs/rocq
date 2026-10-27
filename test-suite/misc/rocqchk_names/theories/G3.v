Declare ML Module "coq-test-suite.bad_name".

Module Type T. Parameter x : Set. End T.

(* The field is in a module N of the implementation of M, which T has not. *)
Module M : T.
  Definition x : Set := nat.
  Module N.
    Test Line Break Axiom zqxbad zqxforged.
  End N.
End M.
