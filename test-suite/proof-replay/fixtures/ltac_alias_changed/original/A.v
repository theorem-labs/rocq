(* target uses the tactic notation solve_it. The edited tree changes its
   body (exact I becomes exact (id I)), so target must miss on the
   tactic_alias read. *)
Tactic Notation "solve_it" := exact I.

Lemma target : True.
Proof. solve_it. Qed.
