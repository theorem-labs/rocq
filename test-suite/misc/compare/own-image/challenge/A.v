(* An answer that relates one of the challenge's OWN levels to one of the
   image's, found by the adversarial review of 0de0865d26.

   The statement stands on the task's own level u and the image's level w,
   which the challenge leaves apart. It is not provable in the challenge's
   graph: w < u is a consistent extension of it, and under w < u no type of
   Type@{w} receives an injection from Type@{u}. The existential and the
   equality are impredicative encodings, so the statement carries no level
   but u and w.

   The honest answer leaves it Admitted -- the config permits that axiom and
   nothing else -- and bad-forged proves it, by putting u below w. The proof
   records u < Img.W.w and writes no Constraint command: this is what a Qed
   can do on its own. *)

Require Img.W.

Monomorphic Universe u.

Monomorphic Definition su : Type@{u} := nat.

Theorem thm : forall R : Prop,
    (forall (T : Type@{Img.W.w}) (f : Type@{u} -> T),
        (forall A B : Type@{u},
            (forall Q : T -> Prop, Q (f A) -> Q (f B)) ->
            forall P : Type@{u} -> Prop, P A -> P B) -> R) -> R.
Proof.
Admitted.
