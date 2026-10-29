(* A plugin loaded after a proof can install closures that a skipped
   tactic would have met in a different state; every proof that opens
   before the last such load runs. *)
Lemma p : True.
Proof. exact I. Qed.
Declare ML Module "rocq-runtime.plugins.btauto".
Lemma q : True.
Proof. exact I. Qed.
