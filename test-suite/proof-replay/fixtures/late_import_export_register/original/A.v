(* An export-locality registration is declared before the first proof, so
   a later Import can rebind a Rocqlib name: the Import is a late command
   again, and the proof before it runs. *)
Definition key_target := 0.
Module R.
#[export] Register key_target as replayfine.test.key.
End R.
Lemma p : True.
Proof. exact I. Qed.
Import R.
Lemma q : True.
Proof. exact I. Qed.
