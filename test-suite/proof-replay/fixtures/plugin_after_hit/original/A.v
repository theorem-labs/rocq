(* A plugin loaded after a proof can install closures that a skipped
   tactic would have met in a different state; the whole file runs without
   replay when one is loaded after its first proof. *)
Lemma p : True.
Proof. exact I. Qed.

Lemma q : True.
Proof. exact I. Qed.
