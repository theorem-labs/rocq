(* The honest answer proves thm from the hidden given of the shared library,
   through the exported Hidden.p. *)

Require Img.Given.

Theorem thm : True.
Proof. exact Img.Given.Hidden.p. Qed.
