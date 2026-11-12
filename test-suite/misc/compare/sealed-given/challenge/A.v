(* The permitted axioms are the task's givens, named by the names they
   print. Top.S.Given.Hidden.ax is hidden by the seal of the pre-checked
   Top.S.Given, so no environment lookup sees it, but its kernel name is
   rooted at that pinned library and it must pass. The bad answers declare
   a module Given.Hidden in the file they may change, so that its axiom
   prints the same name; only its kernel name tells it from the given. *)

Require Top.S.
Require Top.S.Given.

Theorem thm : True.
Proof.
Admitted.
