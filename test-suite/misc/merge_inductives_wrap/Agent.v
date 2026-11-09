(* Spec.v's block, word for word, declared independently: this library does
   not require Spec. *)

Inductive wrap (A : Type) := Wrap : A -> wrap A.

Definition size (w : wrap nat) : nat := match w with Wrap _ a => S a end.

Theorem thm : forall w : wrap nat, size w >= 1.
Proof.
  intro w. destruct w as [a]. simpl. apply le_n_S. apply le_0_n.
Qed.
