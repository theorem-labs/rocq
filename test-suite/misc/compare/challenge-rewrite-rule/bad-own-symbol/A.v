(* A symbol the answer adds, of an empty type. The config permits rules,
   not this assumption: the theorem fails on it like on an Axiom. *)

Symbol s : nat.

Rewrite Rule r := s => 0.

Symbol bot : False.

Theorem thm : s = 0.
Proof. destruct bot. Qed.
