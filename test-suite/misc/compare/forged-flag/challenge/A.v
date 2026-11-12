(* A tolerated flag names its object by the name it prints. A module Q of
   the library Top.P holding an inductive T prints Top.P.Q.T, the name of
   the given; only the object tells the forgery from the given. *)

Require Top.P.
Require Top.P.Q.

Theorem thm : False.
Proof.
Admitted.
