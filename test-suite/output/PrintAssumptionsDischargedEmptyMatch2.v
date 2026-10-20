(* Print Assumptions walks the stored proof term, where the section discharge
   has not run. A match on an Admitted lemma or a section axiom that the
   discharge applies to the section variables is a match on a bare constant
   there, and on an application in the term the discharge builds: only a match
   on a constant that stays bare is reported as "used in ... to prove". *)

Section S.
  Variable u : nat.
  Lemma ax2 : False.
  Proof using u. Admitted.
  Lemma usedin2 : 0 = 0.
  Proof. exact (match ax2 return 0 = 0 with end). Qed.
  Definition usedin2t : 0 = 0 := match ax2 return 0 = 0 with end.
End S.

Print Assumptions usedin2.
Print Assumptions usedin2t.
