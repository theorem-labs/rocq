(* A sealed module and a functor after the first proof: their opening and
   their End stay late commands, so every proof before the functor's End
   runs, the ones inside the two modules included. *)
Module Type T.
End T.
Lemma p : True.
Proof. exact I. Qed.
Module M : T.
Lemma m_inner : True.
Proof. exact I. Qed.
End M.
Module F (X : T).
Lemma f_inner : True.
Proof. exact I. Qed.
End F.
Lemma q : True.
Proof. exact I. Qed.
