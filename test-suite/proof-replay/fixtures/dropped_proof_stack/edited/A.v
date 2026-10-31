(* Each command below drops a proof that is open: Abort All, Succeed around
   a statement, and Fail Fail around a statement. No proof is open after
   it, so the proof that follows it must replay. Abort All is the first
   sentence of the file, so its rewind runs no earlier command again. *)
Lemma dropped_all : True.
Abort All.

Lemma after_abort_all : True.
Proof. exact I. Qed.

Succeed Lemma dropped_succeed : True.

Lemma after_succeed : True.
Proof. exact I. Qed.

Fail Fail Lemma dropped_fail : True.

Lemma after_fail : True.
Proof. exact I. Qed.
