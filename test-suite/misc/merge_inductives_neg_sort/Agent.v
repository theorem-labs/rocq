(* Spec.v's block with the same names in Set instead of Prop: the arity, the
   sort and, with them, what may be eliminated into differ. *)

Inductive p : Set := P0 : p | P1 : p.

Theorem thm : forall x : p, x = x.
Proof. reflexivity. Qed.
