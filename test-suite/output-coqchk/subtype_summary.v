(* A transparently ascribed module beside an opaquely sealed one. The summary
   lists the unsafe fixpoint of both: the transparent one through the final
   environment, the sealed one through the checked implementation, and each
   exactly once. *)
Module A.
Module Sub.
Module Type T. Parameter tgt : 1 = 2. End T.
Module Clear <: T.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.
  Lemma tgt : 1 = 2. Proof. exfalso; exact (loop 0). Qed.
End Clear.
Module Seal : T.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.
  Lemma tgt : 1 = 2. Proof. exfalso; exact (loop 0). Qed.
End Seal.
End Sub.
End A.
