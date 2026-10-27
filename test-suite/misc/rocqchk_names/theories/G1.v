Declare ML Module "coq-test-suite.bad_name".

Module Type T. Parameter x : Set. End T.

(* M is sealed by T, so its implementation has a field that T has not. *)
Module M : T.
  Definition x : Set := nat.
  Test Line Break Axiom zqxbad zqxforged.
End M.
