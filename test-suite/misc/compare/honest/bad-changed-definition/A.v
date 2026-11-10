(* The negative control of the honest check: one character of a challenge
   definition's body is different. *)

Inductive tree : Set := Leaf | Node (l r : tree).

Definition mirror (t : tree) : tree :=
  match t with Leaf => Leaf | Node l r => Node l r end.

Definition U := Type.

Module Type SIG.
  Parameter P : tree -> Prop.
End SIG.

Module M <: SIG.
  Definition P (t : tree) : Prop := t = Leaf.
End M.

Module F (X : SIG).
  Definition Q (t : tree) : Prop := X.P (mirror t).
End F.

Module FM := F M.

Theorem thm : forall t : tree, mirror (mirror t) = t.
Proof. intros t; destruct t; reflexivity. Qed.
