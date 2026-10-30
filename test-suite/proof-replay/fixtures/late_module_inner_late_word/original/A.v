(* A plain module holds a late command (Include), so its End is late too:
   the proof inside the module, after the Include, runs. *)
Module N.
End N.
Lemma p : True.
Proof. exact I. Qed.
Module M.
Include N.
Lemma q : True.
Proof. exact I. Qed.
End M.
Lemma r : True.
Proof. exact I. Qed.
