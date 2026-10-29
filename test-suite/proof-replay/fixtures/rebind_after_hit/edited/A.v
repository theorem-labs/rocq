(* p runs congruence, which forces the process-wide lazies that cache the
   Rocqlib answers for core.eq.* (plugins/cc/cctac.ml). The edited tree
   rebinds core.eq.type to myeq after p. Stock keeps the cached eq, so q's
   congruence still proves its goal; a replay that skipped p's tactics forces
   the lazy only in q, after the rebinding, gets myeq, and q fails (Claude
   review of c2190e74e0, P1). Replay must refuse the whole file. *)
Inductive myeq (A : Type) (x : A) : A -> Prop := myrefl : myeq A x x.

Lemma p : forall x y : nat, x = y -> y = x.
Proof. congruence. Qed.
Register myeq as core.eq.type.
Lemma q : forall x y : bool, x = y -> y = x.
Proof. congruence. Qed.
