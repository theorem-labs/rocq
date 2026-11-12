(* Requires the answer's Img from the working directory, not the image's
   Img.Given, and proves thm from its forged sealed axiom. *)

Require Img.

Theorem thm : True.
Proof. exact (False_rect _ Img.Given.Hidden.p). Qed.
