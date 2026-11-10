(* The shape a task has: a transparent definition, an inductive type, a
   module type, a module with that module type, a functor application, and a
   named theorem whose proof the agent writes. *)

Inductive tree : Set := Leaf | Node (l r : tree).

Definition mirror (t : tree) : tree :=
  match t with Leaf => Leaf | Node l r => Node r l end.

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
Proof.
Admitted.
