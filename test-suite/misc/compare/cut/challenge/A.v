(* A cut: the agent sees one lemma's statement, Admitted, and the lemmas
   below it, also Admitted. Its proof may rest on the given lemmas, which
   the theorem's own permitted list names. *)

Definition two := 2.

Lemma lower : two = 2.
Proof.
Admitted.

Theorem thm : two = 2 /\ two = 2.
Proof.
Admitted.
