(* -proof-record-no-graph: the global graph changes before the proof in a
   way its universe footprint allows (a constraint between levels the proof
   never queries). The rebuilt universe state answers what the declaration
   asks as the recorded one did, so the proof replays. *)
Universe u v x y z.
Constraint u <= v.
Constraint x <= y.
Constraint x <= z.

Lemma universe_grain : Type@{u} -> Type@{v}.
Proof. intros x. exact x. Qed.
