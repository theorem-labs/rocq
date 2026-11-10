(* The same tree, with the proof written. The answer adds a helper lemma
   before a challenge definition, which shifts the number that names every
   monomorphic universe level declared after it, and a file of its own. *)

Inductive tree : Set := Leaf | Node (l r : tree).

Definition mirror (t : tree) : tree :=
  match t with Leaf => Leaf | Node l r => Node r l end.

Definition helper_universe := Type.

Lemma helper : forall t : tree, mirror (mirror t) = t.
Proof. intros t; destruct t; reflexivity. Qed.

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
Proof. exact helper. Qed.
