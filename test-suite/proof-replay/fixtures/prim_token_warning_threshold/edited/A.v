(* target reads the number 3 in probe_scope, whose number notation warns
   above a threshold, and that warning is an error. The edited tree lowers
   the threshold below 3 only: the number still means the same term in the
   same scope, and stock now rejects target with the warning. Replay must
   reject it too. *)
Declare Scope probe_scope.
Number Notation nat Nat.of_num_uint Nat.to_num_uint (warning after 1) : probe_scope.
Open Scope probe_scope.
Set Warnings "+large-number".

Lemma target : nat.
Proof. exact 3. Qed.
