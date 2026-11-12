(* Two honest routes to a permitted axiom that no other case takes: an axiom
   of a shared library both sides load (Img.Classical.classic), and a given
   reached through a module alias (Top.P.Q.N.j). *)

Require Img.Classical.
Require Top.P.Q.

Theorem thm : (0 = 1 \/ ~ 0 = 1) /\ 0 = 1.
Proof.
Admitted.
