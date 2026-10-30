(* [same] and [changed] each read a number in the open scopes, my_scope
   first. Before [same], my_scope has no number notation, so [same] reads its
   number in nat_scope. Between the two proofs a number notation for nat is
   declared: in other_scope in the original tree, in my_scope in the edited
   one. So [changed] reads its number in nat_scope at registration and in
   my_scope now, and must miss on that read; [same] must replay. Both trees
   declare one number notation there, so the universe counters at [changed]
   are the same in both. *)
Declare Scope my_scope.
Declare Scope other_scope.
Open Scope my_scope.

Lemma same : nat.
Proof. exact 2. Qed.

Number Notation nat Nat.of_num_uint Nat.to_num_uint : other_scope.

Lemma changed : nat.
Proof. exact 3. Qed.
