(* `do N idtac` is deterministic, allocates nothing and is none of the
   ineligible tactics (`Time` and `Timeout` are).

   The three times this file has to separate, for a 240 s budget:
     charge of the two replayed proofs  <  budget  <  the stock compile.
   The charge uses each proof's REGISTERED wall time, which carries the
   recorder's overhead, so the registered proof must stay under half the
   budget while three grade proofs must run well past it.  That puts the
   grade's proof at about 240/2.6 = 92 s.

   Measured on speed-r1 against a build of 588a2ebc, 2026-10-25:
   400,000,000 iterations gave 93.2, 86.2 and 80.3 s per proof when recording
   and 236 s for the three in a stock grade compile, which is 79 s each and
   only 4 s under the budget — the stock compile was never killed, so the
   fixture could not fail.  470,000,000 is that scaled to about 92 s a proof:
   roughly 277 s for the stock compile and a charge of about 202 s after two
   hits, which leaves about 38 s of budget to be spent inside the third
   proof. *)
Ltac burn := do 470000000 idtac.

Lemma slow1 : True.
Proof. burn. exact I. Qed.

Lemma slow2 : True.
Proof. burn. exact I. Qed.

Lemma slow3 : True.
Proof. burn. exact I. Qed.
