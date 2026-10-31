(* A Require of a library that carries a Register is late while the
   library is not loaded: the proof before it runs its tactics. Once the
   library is loaded, a second Require of it applies no Register, so the
   proof between the two replays. *)
Lemma p : True.
Proof. exact I. Qed.
Require PR.Reg.
Lemma q : True.
Proof. exact I. Qed.
Require PR.Reg.
Lemma r : True.
Proof. exact I. Qed.
