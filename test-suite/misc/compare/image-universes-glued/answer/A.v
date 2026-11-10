Require Img.Glue.
Require Img.V.
Require Img.W.

Theorem thm : forall R : Prop,
    (forall (T : Type@{Img.W.w}) (f : Type@{Img.V.v} -> T),
        (forall A B : Type@{Img.V.v},
            (forall Q : T -> Prop, Q (f A) -> Q (f B)) ->
            forall P : Type@{Img.V.v} -> Prop, P A -> P B) -> R) -> R.
Proof.
  intros R k. apply (k Type@{Img.V.v} (fun X => X)). intros A B H. exact H.
Qed.
