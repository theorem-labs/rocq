(* The warning deprecated-intros-until-0 is an error, and target's try
   catches it: stock accepts target. Raising the recorded warning again on a
   replay would reject it, so a proof that raises a warning as an error is
   not replayed. control raises none and replays. Both trees are the same. *)
Set Warnings "+deprecated-intros-until-0".

Lemma target : True.
Proof.
  try intros until 0.
  exact I.
Qed.

Lemma control : True.
Proof. exact I. Qed.
