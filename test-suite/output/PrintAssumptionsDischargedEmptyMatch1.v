(* Print Assumptions walks the stored proof term, where the section discharge
   has not run. A match on an Admitted lemma or a section axiom that the
   discharge applies to the section variables is a match on a bare constant
   there, and on an application in the term the discharge builds: only a match
   on a constant that stays bare is reported as "used in ... to prove". *)

Section S.
  Variable u : nat.
  Definition k := u + 1.
  Lemma ax : (fun _ : nat => False) u.
  Proof. Admitted.
  Lemma usedin1 : k = k.
  Proof. exact (match ax return k = k with end). Qed.

  Lemma ax2 : False.
  Proof using u. Admitted.
  Lemma usedin2 : k = k.
  Proof. exact (match ax2 return k = k with end). Qed.

  Hypothesis h : False.
  Lemma usedin3 : k = k.
  Proof. exact (match h return k = k with end). Qed.
End S.

Print Assumptions usedin1.
Print Assumptions usedin2.
Print Assumptions usedin3.

Module Type T. Axiom bad : False. End T.
Module F (X : T).
  Lemma usedinF : 0 = 0. Proof. exact (match X.bad return 0 = 0 with end). Qed.
End F.
Module XI. Axiom bad : False. End XI.
Module FI := F XI.
Print Assumptions FI.usedinF.

Section P.
  Universe w.
  Polymorphic Definition kp@{v} (A : Type@{v}) := A.
  Axiom badp : False.
  Polymorphic Lemma usedinP@{v} : kp@{v} nat = kp@{v} nat.
  Proof. exact (match badp return _ with end). Qed.
End P.
Print Assumptions usedinP.
