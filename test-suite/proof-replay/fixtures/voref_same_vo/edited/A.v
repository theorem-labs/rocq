(* The same proofs replay to the same .vo bytes whether the registration
   kept their terms inline or as references into its .vo
   (alt_register_flags): a plain lemma, a polymorphic lemma whose term names
   its level, and in a section a lemma over a variable, an opaque Let and a
   lemma over that Let. The edited tree changes a definition no proof
   reads. *)
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
