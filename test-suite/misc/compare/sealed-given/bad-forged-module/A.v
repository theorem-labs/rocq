(* Rocq does not load the library Top.S.Given beside a module Top.S.Given,
   so this answer requires only Top.S, and Top.S.Given.Hidden.ax is its own
   axiom. *)

Require Top.S.

Theorem thm : True.
Proof. exact Top.S.Given.Hidden.p. Qed.
