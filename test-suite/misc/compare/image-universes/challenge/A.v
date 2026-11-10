(* The residual this rule leaves, written down.

   The statement stands on two of the IMAGE's levels, v and w, which the
   image leaves apart, and the answer's proof puts v below w. The comparator
   PASSES it: a constraint between two of the image's levels is the one
   shape the answer may add, because a proof adds those by instantiating the
   image's definitions and every real proof does -- the task's key and its
   untouched control each failed on one (dispatch://BET-901).

   Today's grade of record passes it too: a Checker file that Requires this
   statement and that proof, ascribes the proof's constant to the
   statement's module type and compiles, which it does, since the
   ascription asks about the type and the kernel has already merged the
   proof's constraints into the one environment. So this is the bar the
   comparator replaces, not a step below it. A statement that stands on two
   of the image's levels relative to each other is the shape to avoid when
   writing a task. *)

Require Img.V.
Require Img.W.

Theorem thm : forall R : Prop,
    (forall (T : Type@{Img.W.w}) (f : Type@{Img.V.v} -> T),
        (forall A B : Type@{Img.V.v},
            (forall Q : T -> Prop, Q (f A) -> Q (f B)) ->
            forall P : Type@{Img.V.v} -> Prop, P A -> P B) -> R) -> R.
Proof.
Admitted.
