(* An honest answer that declares a symbol and no rewrite rule. A symbol is
   not a rule: the config forbids rules, and this answer has none. Nothing
   reaches the symbol, so no proof rests on it. *)

Symbol s : nat.

Definition two := 2.

Theorem thm : two = 2.
Proof. reflexivity. Qed.
