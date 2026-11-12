(* A symbol with no rule is an assumption. One of an empty type proves the
   theorem, and the axiom check counts it like an Axiom: the config permits
   no axiom, so the theorem fails on it. *)

Symbol bot : False.

Definition two := 2.

Theorem thm : two = 2.
Proof. destruct bot. Qed.
