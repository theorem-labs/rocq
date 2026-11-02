(* A Require that loads a plugin is late: the proof before it runs its
   tactics. Once the library is loaded, a second Require of it loads no
   plugin, so the proof between the two replays. *)
Lemma p : True.
Proof. exact I. Qed.
Require PR.Plug.
Lemma q : True.
Proof. exact I. Qed.
Require PR.Plug.
Lemma r : True.
Proof. exact I. Qed.
