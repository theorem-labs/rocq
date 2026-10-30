(* The warning deprecated-intros-until-0 is an error, and target's sentence
   turns it back into a plain warning for that sentence only (a warnings
   attribute): stock accepts target. Raising the warning again after a
   replay, outside the attribute, would reject it. A proof that raises a
   warning is not replayed. control raises none and replays. Both trees are
   the same. *)
Set Warnings "+deprecated-intros-until-0".

Lemma target : True.
Proof.
  #[warnings="deprecated-intros-until-0"] intros until 0.
  exact I.
Qed.

Lemma control : True.
Proof. exact I. Qed.
