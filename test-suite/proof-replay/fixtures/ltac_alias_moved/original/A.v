(* target uses the tactic notation solve_it. The edited tree moves the
   notation down three lines and keeps its body: only its source locations
   change, so target must replay. *)
Tactic Notation "solve_it" := exact I.

Lemma target : True.
Proof. solve_it. Qed.
