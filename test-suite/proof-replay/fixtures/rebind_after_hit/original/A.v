(* Every proof that opens before a late Rocqlib rebinding runs: [p] forces
   congruence's cached equality before the edited tree registers [myeq], as
   stock does. A replayed proof that only met the cached value would read
   nothing, so the rule is by position. The rebinding trips the Rocqlib
   fence, so [q] runs too. *)
Inductive myeq (A : Type) (x : A) : A -> Prop := myrefl : myeq A x x.

Lemma untouched : True.
Proof. exact I. Qed.

Lemma p : forall x y : nat, x = y -> y = x.
Proof. congruence. Qed.

Lemma q : forall x y : bool, x = y -> y = x.
Proof. congruence. Qed.
