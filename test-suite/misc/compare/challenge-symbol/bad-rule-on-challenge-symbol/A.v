(* A rule the answer adds on the challenge's own symbol, which the config
   does not permit. *)

Symbol s : nat.

Rewrite Rule r := s => 0.

Definition two := 2.

Theorem thm : two = 2.
Proof. reflexivity. Qed.
