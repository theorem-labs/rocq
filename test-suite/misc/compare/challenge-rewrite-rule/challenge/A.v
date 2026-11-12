(* A task that declares a symbol and a rewrite rule on it, under a config
   that permits rules (dispatch://BET-895, P1-3). The theorem rests on the
   symbol, which is an assumption like an Axiom, so the config permits it
   by name. *)

Symbol s : nat.

Rewrite Rule r := s => 0.

Theorem thm : s = 0.
Proof.
Admitted.
