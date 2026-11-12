(* A task that declares a symbol and no rewrite rule (dispatch://BET-895,
   P1-3). Loading the challenge must not stop on the symbol, and the
   symbol, being the challenge's own, is no rule of the answer's. *)

Symbol s : nat.

Definition two := 2.

Theorem thm : two = 2.
Proof.
Admitted.
