(* The challenge holds a real proof of thm, and a given lemma that a cut
   task would hand the agent. An answer that proves thm another way must
   report its own axioms, never the challenge's: the challenge's proof body
   is in a second environment and can never stand in for the answer's. *)

Definition two := 2.

Lemma given : two = 2.
Proof. reflexivity. Qed.

Theorem thm : two = 2.
Proof. exact given. Qed.
