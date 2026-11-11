(* The same statement as image-universes, where the image's Glue already
   relates v and w. The answer's proof adds nothing, and it passes for a
   reason that does not rest on the rule: the challenge's own environment
   stands on the constraint the proof needs.

   Img.Glue is Required here, so the challenge's own closure reaches it. *)

Require Img.Glue.
Require Img.V.
Require Img.W.

Theorem thm : forall R : Prop,
    (forall (T : Type@{Img.W.w}) (f : Type@{Img.V.v} -> T),
        (forall A B : Type@{Img.V.v},
            (forall Q : T -> Prop, Q (f A) -> Q (f B)) ->
            forall P : Type@{Img.V.v} -> Prop, P A -> P B) -> R) -> R.
Proof.
Admitted.
