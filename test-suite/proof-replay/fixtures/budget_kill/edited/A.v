(* `do N idtac` is deterministic, allocates nothing and is none of the
   ineligible tactics (`Time` and `Timeout` are).

   The runner sets the budget from this machine's registration: the
   recorded wall times of slow1 and slow2 (the charge of the two hits) plus
   0.3 of slow3's.  The three times then separate on a slow box as on a
   fast one:  charge  <  budget  <  the stock compile, and the budget runs
   out inside slow3's tactic.  The fixed 240 s budget before it held only
   near the speed of the box it was tuned on: on speed-pool-39 (4 CPUs,
   beside other fixtures, 2026-10-31) each recorded proof took about 126 s,
   so the charge of the two hits was 252 s and the replay compile was killed
   before slow3 opened.

   Measured on speed-r1 against a build of 588a2ebc, 2026-10-25:
   400,000,000 iterations gave 93.2, 86.2 and 80.3 s per proof when recording
   and 79 s per proof in a stock grade compile.  470,000,000 makes each proof
   about 92 s there, long against the noise of a shared machine. *)
Ltac burn := do 470000000 idtac.

Lemma slow1 : True.
Proof. burn. exact I. Qed.

Lemma slow2 : True.
Proof. burn. exact I. Qed.

Lemma slow3 : True.
Proof. idtac. burn. exact I. Qed.
