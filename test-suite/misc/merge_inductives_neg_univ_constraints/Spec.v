#[universes(polymorphic)]
Inductive b@{u v} (A1 : Type@{u}) (A2 : Type@{v}) := Mk : A1 -> A2 -> b A1 A2.

(* The instance is spelled out so that both libraries speak of the same one:
   [Set <= Set] holds, so it satisfies the agent's extra constraint too, and
   what is left to tell the two blocks apart is the constraint itself. *)
Definition Stmt := forall x : b@{Set Set} nat nat, x = x.
