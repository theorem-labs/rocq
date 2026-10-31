(* A Require that loads a library is late: the proof before it runs its
   tactics. Once the library is loaded, a second Require of it loads
   nothing, so the proof between the two replays. *)
Lemma p : True.
Proof. exact I. Qed.
Require PR.Lib.
Lemma q : True.
Proof. exact I. Qed.
Require PR.Lib.
Lemma r : True.
Proof. exact I. Qed.
