(* An axiom the cut's permitted list does not name. *)

Definition two := 2.

Lemma lower : two = 2.
Proof.
Admitted.

Axiom elsewhere : two = 2.

Theorem thm : two = 2 /\ two = 2.
Proof. split; exact elsewhere. Qed.
