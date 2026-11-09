Require SpecN.
Require AgentN.

(* Merging the two copies of [wrap] makes the two universes one. Asking for
   one to be below the other is then a contradiction, and must be reported as
   one. *)
Constraint SpecN.u < AgentN.u.
