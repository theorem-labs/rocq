(* The same block as misc/merge_inductives_wrap, declared monomorphic. An
   [Inductive wrap (A : Type)] with no attribute is made template polymorphic
   automatically (vernac/comInductive.ml); spelling the attribute out is the
   only way to get the other case, a block whose universe level each file
   declares for itself, so that the two copies match only once the levels are
   matched by the bijection and equated. *)
#[universes(template=no)]
Inductive wrap (A : Type) := Wrap : A -> wrap A.

Definition size (w : wrap nat) : nat := match w with Wrap _ a => S a end.

Theorem thm : forall w : wrap nat, size w >= 1.
Proof. intro w. destruct w as [a]. simpl. apply le_n_S. apply le_0_n. Qed.
