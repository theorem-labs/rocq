(* Spec.v's two inductive blocks, word for word, declared independently: this
   library does not require Spec. *)

Inductive color := Red | Green.

Inductive tree := Leaf : color -> tree | Node : tree -> tree -> tree.

Fixpoint size (t : tree) : nat :=
  match t with Leaf _ => 1 | Node a b => size a + size b end.

Theorem thm : forall t : tree, size t >= 1.
Proof.
  induction t as [c | a IHa b IHb]; simpl.
  - apply le_n.
  - revert IHa. destruct (size a) as [|n]; simpl.
    + intro H; inversion H.
    + intros _. apply le_n_S. apply le_0_n.
Qed.
