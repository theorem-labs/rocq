(* An unrelated universe constraint changes before the proof.  The proof only
   needs the relation between u and v, so per-query replay must still hit. *)
Universe u v x y z.
Constraint u <= v.
Constraint x <= y.

Lemma universe_grain : Type@{u} -> Type@{v}.
Proof. intros x. exact x. Qed.
