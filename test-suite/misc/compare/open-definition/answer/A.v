(* The honest answer leaves P and P0 as they are and proves thm from P0. *)

Parameter P : nat -> Prop.

Axiom P0 : P 0.

Theorem thm : P 0.
Proof. exact P0. Qed.
