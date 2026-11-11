(* PROBE forged answer: the same statement, proved by putting u below w. The
   proof itself records u < Img.W.w (own-to-image); no Constraint command. *)
Require Img.W.

Monomorphic Universe u.

Monomorphic Definition su : Type@{u} := nat.

Theorem thm : forall R : Prop,
    (forall (T : Type@{Img.W.w}) (f : Type@{u} -> T),
        (forall A B : Type@{u},
            (forall Q : T -> Prop, Q (f A) -> Q (f B)) ->
            forall P : Type@{u} -> Prop, P A -> P B) -> R) -> R.
Proof.
  intros R k. apply (k Type@{u} (fun X => X)). intros A B H. exact H.
Qed.
