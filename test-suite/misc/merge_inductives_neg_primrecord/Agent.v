(* Spec.v's record word for word, without Primitive Projections: the block is
   a regular record, its projections are constants and it has no definitional
   eta. *)

Record r := Mk { r_fst : nat; r_snd : nat }.

Theorem thm : forall x : r, x = x.
Proof. reflexivity. Qed.
