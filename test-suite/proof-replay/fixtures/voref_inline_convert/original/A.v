(* rocq proof-record-inline. The registration stores three terms as
   references into its .vo (plus_zero, k_plus_zero, l_eq) and two inline
   (the polymorphic id_type, the section Let l). The fixture converts each
   record with its .vo and publishes the converted record WITHOUT the .vo
   (vo_mutation remove): every proof must still replay, to the .vo stock
   makes and to the .vo the vo-ref record replays to with its object. *)
Definition unrelated := 3.

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
