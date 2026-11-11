(* The tolerance must not hide a constraint the challenge requires. *)

Monomorphic Universe u.
Monomorphic Universe v.

Monomorphic Constraint v <= u.

Monomorphic Definition Spec : Type@{u+1} := Type@{u}.
Monomorphic Definition Marker : Type@{v} := nat.

Theorem thm : forall R : Prop,
    (forall (T : Type) (f : Spec -> T),
        (forall A B : Spec,
            (forall Q : T -> Prop, Q (f A) -> Q (f B)) ->
            forall P : Spec -> Prop, P A -> P B) -> R) -> R.
Proof.
  intros R k.
  apply (k Spec (fun X => X)).
  intros A B H.
  exact (eq_rect A (fun _ => forall Q : Spec -> Prop, Q A -> Q B) H A eq_refl).
Qed.
