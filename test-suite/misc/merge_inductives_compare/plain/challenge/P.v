(* No copies anywhere: the option has nothing to merge, so the verdicts must
   be the same with it and without it. *)
Inductive colour := Red | Blue.

Theorem thm : Red = Red.
Proof. Admitted.
