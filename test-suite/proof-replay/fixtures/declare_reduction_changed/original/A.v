(* p reduces a beta redex with the named reduction rr and checks that the
   result is a variable. The proof's sentences hold the name rr, not its
   definition. The edited tree declares rr as cbv iota, which does not
   reduce the redex, and changes nothing in p's key: not its statement, its
   sentences or its position. Stock now fails is_var, so replay must not
   install the stored term (cross-family review of 079bc4cb71, finding CF3,
   trigger T3). *)
Declare Reduction rr := cbv beta.

Lemma p : forall n : nat, True.
Proof.
  intro n.
  let t := eval rr in ((fun x : nat => x) n) in
  is_var t.
  exact I.
Qed.
