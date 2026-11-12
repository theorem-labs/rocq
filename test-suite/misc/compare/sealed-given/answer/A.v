(* The honest answer proves thm from the hidden given of the pre-checked
   file, through the exported Hidden.p. *)

Require Top.S.
Require Top.S.Given.

Theorem thm : True.
Proof. exact Top.S.Given.Hidden.p. Qed.
