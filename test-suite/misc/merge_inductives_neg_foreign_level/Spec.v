Require Shared.

(* The parameter's sort is a THIRD library's level, not Spec's own. *)
#[universes(template=no)]
Inductive b (A : Type@{Shared.w}) := B0 : A -> b A.

Definition Stmt := forall x : b nat, x = x.
