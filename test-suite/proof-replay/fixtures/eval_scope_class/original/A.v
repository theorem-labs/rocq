(* [same] reads the scope bound to U and [changed] the scope bound to T, each
   through a cast of zz to that type. The edited tree binds T to b_scope, so
   [changed] must miss on that read. zz means 0 in both scopes, so the two
   compiles give the same term. U's scope does not change, so [same] must
   replay (gate review, breadth audit gap BA1). *)
Declare Scope a_scope.
Declare Scope b_scope.
Notation "'zz'" := 0 : a_scope.
Notation "'zz'" := 0 : b_scope.
Definition T := nat.
Definition U := nat.
Bind Scope a_scope with T.
Bind Scope a_scope with U.

Lemma same : U.
Proof. exact (zz : U). Qed.

Lemma changed : T.
Proof. exact (zz : T). Qed.
