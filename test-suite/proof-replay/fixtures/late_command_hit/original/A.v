(* A late command loads code after the first proof. The proof before the
   last late command runs; the proof after it meets the state stock meets,
   so it replays. *)
Lemma p : True.
Proof. exact I. Qed.
Declare ML Module "rocq-runtime.plugins.btauto".
Lemma q : True.
Proof. exact I. Qed.
