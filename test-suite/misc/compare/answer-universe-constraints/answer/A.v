(* This Qed proof uses Corelib's monomorphic [eq_rect] at [Spec].
   Cumulativity adds [Spec]'s level below [eq_rect]'s Corelib level. The
   challenge's Admitted proof has no such edge. *)

Monomorphic Universe u.
Monomorphic Universe v.

Monomorphic Constraint u < v.

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
