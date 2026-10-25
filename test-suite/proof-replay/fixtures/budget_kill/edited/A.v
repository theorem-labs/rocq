(* `do N idtac` is deterministic, allocates nothing and is none of the
   ineligible tactics (`Time` and `Timeout` are).  Measured on speed-r1 with
   the recorder at d97df04b, under the box's own load: 440,000,000 iterations
   took 116.6, 120.2 and 115.5 s of proof wall time, 370,000,000 took 81.2,
   89.9 and 97.6 s, so 400,000,000 is about 100 s. *)
Ltac burn := do 400000000 idtac.

Lemma slow1 : True.
Proof. burn. exact I. Qed.

Lemma slow2 : True.
Proof. burn. exact I. Qed.

Lemma slow3 : True.
Proof. idtac. burn. exact I. Qed.
