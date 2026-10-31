(* The registered .vo beside the record is not the one the registration
   wrote: one byte of its opaque proofs changed (vo_mutation change), so it
   no longer hashes to the record's vo_opaques. The proof that refers to it
   misses on vo_term and runs its tactics; the polymorphic lemma, whose term
   is inline, replays. *)
Definition unrelated := 3.

Lemma plus_zero : forall n : nat, n + 0 = n.
Proof. induction n as [|n IHn]; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Polymorphic Lemma id_type@{u} : Type@{u} -> Type@{u}.
Proof. exact (fun x => x). Qed.
