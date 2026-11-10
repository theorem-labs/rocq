(* An open definition is a spec non-goal: the challenge states properties
   of P, and the answer must not get to choose what P is. In a .vo an
   Admitted lemma, an Axiom and a Parameter are the same declaration, so
   what separates a proof the agent must write from a definition it must
   not is the sort of the type: P0 is a proposition, P is data. *)

Parameter P : nat -> Prop.

Axiom P0 : P 0.

Theorem thm : P 0.
Proof.
Admitted.
