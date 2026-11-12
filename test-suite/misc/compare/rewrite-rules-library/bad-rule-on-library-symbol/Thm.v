(* The rewrite rule is declared in the challenge's own file, on a symbol of
   a library the answer added (dispatch://BET-895, P1-1). *)

Require Top.Pin.

Rewrite Rule r := Top.Pin.s => 0.

Definition two := 2.

Theorem thm : two = 2.
Proof. reflexivity. Qed.
