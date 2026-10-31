(* -proof-record-vo-ref: the registration stores this proof's term as its
   index in the opaque proofs of its own .vo, once it has compared that the
   term there is the term it declared. The edited tree changes a definition
   the proof never reads, so the proof replays, its term read from the
   registered .vo. *)
Definition unrelated := 3.

Lemma plus_zero : forall n : nat, n + 0 = n.
Proof. induction n as [|n IHn]; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.
