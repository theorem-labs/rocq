(* [lift] queries whether its two instantiated universe levels satisfy the
   declared non-strict constraint. The proof asks it at u and v. *)
Polymorphic Definition lift@{a b | a <= b} (A : Type@{a}) : Type@{b} := A.

Universe u v.
Constraint u < v.

Lemma universe_changed : Type@{u} -> Type@{v}.
Proof. intros x. exact (@lift@{u v} x). Qed.
