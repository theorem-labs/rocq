(* Spec.v's block word for word, asked not to be template polymorphic. The
   attribute has to be spelled out: an [Inductive w (A : Type)] with no
   attribute at all is made template automatically, which would leave the two
   declarations the same. *)

#[universes(template=no)]
Inductive w (A : Type) := W : A -> w A.

Theorem thm : forall x : w nat, x = x.
Proof. reflexivity. Qed.
