(* An Import after the first proof, inside a plain module, with no
   export-locality registration loaded: neither the Import nor the module's
   End is a late command, so every proof replays. *)
Lemma p : True.
Proof. exact I. Qed.
Module M.
Import Nat.
Lemma q : True.
Proof. exact I. Qed.
End M.
Lemma r : True.
Proof. exact I. Qed.
