Require Spec.
Require Agent.

(* The agent's theorem is about its own first and second constructors. A merge
   keeps constructor positions, so granting one here would make this
   typecheck: the agent's [Green] would be the spec's [Red] and the agent's
   [Red] the spec's [Green]. *)
Definition chk : Spec.Stmt := Agent.thm.
