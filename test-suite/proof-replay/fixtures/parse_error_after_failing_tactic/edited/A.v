(* The registration proves target. The edited tree keeps its statement, so
   replay holds a candidate for it and parses its sentences ahead. A tactic
   fails, and the sentence after it does not parse. Stock stops at the
   tactic and reports its error. Replay must report the same error, not the
   syntax error. *)
Lemma target : True.
Proof.
  fail "the tactic fails first".
  exact (.
Qed.
