(* Print Assumptions reuses traversals across queries in one environment.
   A Require in the middle of a file changes the environment. *)

Axiom ax : nat.
Definition d := ax.
Print Assumptions d.
Require Import TestSuite.module_bug7192.
Print Assumptions d.
Print Assumptions M7192.D.f.
Print Assumptions M7192.D.f.
Require Import TestSuite.module_bug8416.
Print Assumptions M8416.f.
Print Assumptions d.
