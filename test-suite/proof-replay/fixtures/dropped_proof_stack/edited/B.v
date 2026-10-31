(* Reset drops the proof that is open. No proof is open after it, so the
   proof that follows it must replay. The rewind goes back to the state
   after anchor, so no proof runs again. *)
Definition anchor := 0.

Lemma dropped_reset : True.
Reset dropped_reset.

Lemma after_reset : True.
Proof. exact I. Qed.
