(* Spec.v's two constructors, in the other order. *)

Inductive color := Green | Red.

Theorem thm : Green <> Red.
Proof. discriminate. Qed.
