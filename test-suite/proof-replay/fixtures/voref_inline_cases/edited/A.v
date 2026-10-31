(* Which proofs keep an inline term under -proof-record-vo-ref. The fixture
   publishes the records WITHOUT the registered .vo (vo_mutation remove): a
   proof that refers to the .vo misses on vo_term, and a proof whose term is
   inline replays. The registration writes a reference only when the term in
   the .vo's opaque table is the term it declared: the polymorphic lemma's
   term names its level, which the table holds abstracted; the opaque Let is
   a section variable, which has no table entry at all. *)
Definition unrelated := 4.

Lemma plus_zero : forall n : nat, n + 0 = n.
Proof. induction n as [|n IHn]; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Polymorphic Lemma id_type@{u} : Type@{u} -> Type@{u}.
Proof. exact (fun x => x). Qed.

Section S.
Variable k : nat.

Lemma k_plus_zero : k + 0 = k.
Proof. rewrite <- plus_n_O. reflexivity. Qed.

Let l : nat.
Proof. exact k. Qed.

Lemma l_eq : l = l.
Proof. reflexivity. Qed.
End S.
