(* Each proof reads one constant of A. Only the proof that reads the
   unchanged t0 replays. *)
Require Import PR.A.
Lemma u0 : True. Proof. pose t0. exact I. Qed.
Lemma u1 : True. Proof. pose t1. exact I. Qed.
Lemma u2 : True. Proof. pose t2. exact I. Qed.
Lemma u3 : True. Proof. pose (t3 nat). exact I. Qed.
Lemma u4 : True. Proof. pose t4. exact I. Qed.
Lemma u5 : True. Proof. pose C5. exact I. Qed.
