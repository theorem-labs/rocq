(* Three honest routes to a permitted axiom that no other case takes: an
   axiom of a shared library both sides load (Img.Classical.classic), and a
   given (Top.P.Q.N.j) reached through a module alias and through an
   Include of its module. *)

Require Img.Classical.
Require Top.P.Q.

Theorem thm : (0 = 1 \/ ~ 0 = 1) /\ 0 = 1 /\ 1 = 2.
Proof.
Admitted.
