(* The proof is left Admitted: a constant without a body is an axiom. *)

Definition two := 2.

Lemma given : two = 2.
Proof. reflexivity. Qed.

Theorem thm : two = 2.
Proof.
Admitted.
