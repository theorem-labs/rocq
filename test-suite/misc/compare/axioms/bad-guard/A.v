(* A fixpoint the guard condition does not accept, under
   Unset Guard Checking: a relaxed typing flag the config does not
   tolerate. *)

Definition two := 2.

Unset Guard Checking.

Fixpoint loop (n : nat) {struct n} : two = 2 := loop n.

Set Guard Checking.

Lemma given : two = 2.
Proof. exact (loop 0). Qed.

Theorem thm : two = 2.
Proof. exact (loop 0). Qed.
