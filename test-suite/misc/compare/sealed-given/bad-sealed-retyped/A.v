(* The challenge exports the given Top.S.E.ex : True. This answer seals E,
   hides an axiom of that kernel name at another type, False, and proves
   thm from it through the exported E.bad. The declaration comparison
   finds the challenge's E.ex missing from the answer; the axiom rule
   refuses it too, since the answer does not export that name. *)

Require Top.S.
Require Top.S.Given.

Theorem thm : True.
Proof. exact (False_rect _ Top.S.E.bad). Qed.
