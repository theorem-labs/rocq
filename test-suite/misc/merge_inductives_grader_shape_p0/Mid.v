Require Spec.
Require Agent.

(* Typed only under the merge: the scrutinee is built with the agent's
   constructor and matched at the spec's type, which also moves a value
   between the two libraries' universe levels. *)
Definition down (X : Type@{Agent.u}) : Type@{Spec.u} :=
  match (Agent.mk X : Spec.box) return Type@{Spec.u} with Spec.mk Y => Y end.
