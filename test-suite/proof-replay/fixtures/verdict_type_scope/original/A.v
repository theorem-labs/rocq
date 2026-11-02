(* The cast [(zz : T)] interprets zz in the scope that Bind Scope attaches to
   T. The edited tree binds T to b_scope, where zz has no interpretation, so
   the stock script fails. Replay must fail too: the recorded notation query
   names a_scope, which still answers, so only a read of the scope that T
   selects sees the edit (gate review, breadth audit gap BA1). A cast, not
   [exact zz] against the goal T: Ltac interprets the term of [exact]
   without its expected type (plugins/ltac/tacinterp.ml, [interp_gen]). *)
Declare Scope a_scope.
Declare Scope b_scope.
Notation "'zz'" := 0 : a_scope.
Definition T := nat.
Bind Scope a_scope with T.

Lemma p : T.
Proof. exact (zz : T). Qed.
