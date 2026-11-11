(* The universe tolerance must not permit a changed theorem statement. *)

Monomorphic Universe u.
Monomorphic Universe v.

Monomorphic Constraint u < v.

Monomorphic Definition Spec : Type@{u+1} := Type@{u}.
Monomorphic Definition Marker : Type@{v} := nat.

Theorem thm : forall R : Prop, R -> R.
Proof.
  intros R r.
  exact r.
Qed.
