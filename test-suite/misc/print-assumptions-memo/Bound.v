(* Every query here weighs the same: one definition over its own axiom. After
   five disjoint queries the entries weigh five times the heaviest query, more
   than the bound of four, so they are cleared before the sixth: g0 is walked
   again rather than replayed, and replayed on the seventh. *)

Axiom a0 : Prop.
Axiom a1 : Prop.
Axiom a2 : Prop.
Axiom a3 : Prop.
Axiom a4 : Prop.
Definition g0 := a0.
Definition g1 := a1.
Definition g2 := a2.
Definition g3 := a3.
Definition g4 := a4.
Print Assumptions g0.
Print Assumptions g1.
Print Assumptions g2.
Print Assumptions g3.
Print Assumptions g4.
Print Assumptions g0.
Print Assumptions g0.
