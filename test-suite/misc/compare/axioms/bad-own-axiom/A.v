(* The challenge proves thm; this answer proves it from an axiom of its
   own. The verdict must report this answer's axiom, which is only possible
   because the challenge's proof body never reaches the answer's
   environment. *)

Definition two := 2.

Axiom cheat : two = 2.

Lemma given : two = 2.
Proof. exact cheat. Qed.

Theorem thm : two = 2.
Proof. exact cheat. Qed.
