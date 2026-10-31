(* -proof-record-no-graph: each stored term leaves out the global universe
   graph, and replay rebuilds the proof's universe state from its own graph,
   then checks what the rebuilt graphs answer against the recorded digest.
   Both proofs replay, to the same .vo as from a record that keeps the graph
   (alt_register_flags), and each stored term is a few kB. *)
Universe u v.
Constraint u <= v.

Definition unrelated := 4.

Lemma universe_grain : Type@{u} -> Type@{v}.
Proof. intros x. exact x. Qed.

Polymorphic Lemma id_type@{w} : Type@{w} -> Type@{w}.
Proof. exact (fun x => x). Qed.
