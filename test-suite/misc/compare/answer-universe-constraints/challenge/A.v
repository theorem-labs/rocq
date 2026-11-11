(* The statement is a task-shaped monomorphic specification. Its proof is
   admitted in the challenge, so its universe graph does not include the
   Corelib constraint that the answer's Qed proof needs. *)

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
Admitted.
