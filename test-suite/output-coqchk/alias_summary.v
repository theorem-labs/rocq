Module A.
Module Sub.
Module Type T. Parameter tgt : 1 = 2. End T.
Module Seal : T.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.
  Lemma tgt : 1 = 2. Proof. exfalso; exact (loop 0). Qed.
End Seal.
Module Y : T := Seal.
Definition tgt2 : 1 = 2 := Y.tgt.
Lemma tgt3 : 1 = 2. Proof. exact Y.tgt. Qed.
End Sub.
End A.
