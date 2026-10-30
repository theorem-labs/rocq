(* [same] reads the delimiting key k1 and [changed] reads k2. The edited tree
   binds k2 to another scope, so [changed] must miss on that read; k1 does
   not change, so [same] must replay. *)
Declare Scope s1_scope.
Declare Scope s2_scope.
Declare Scope s3_scope.
Delimit Scope s1_scope with k1.
Delimit Scope s2_scope with k2.

Lemma same : bool.
Proof. exact (true)%k1. Qed.

Lemma changed : bool.
Proof. exact (false)%k2. Qed.
