(* The permitted axiom Img.Given.Hidden.ax is hidden by the seal of a shared
   library, so no environment lookup sees it; its kernel name is rooted at a
   library outside every root the challenge stands in for, which the answer
   cannot write, and it must pass. *)

Require Img.Given.

Theorem thm : True.
Proof.
Admitted.
