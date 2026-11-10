Universe u.

(* The one difference from SpecS.v: a constraint against Set, a level both
   libraries share. The declaration below is SpecS.v's, word for word. *)
Constraint Set < u.

Inductive b (A : Type@{u}) := B : A -> b A.

Theorem thm : forall x : b nat, x = x.
Proof. reflexivity. Qed.
