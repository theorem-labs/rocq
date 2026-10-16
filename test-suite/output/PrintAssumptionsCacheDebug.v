(* Print Assumptions reuses traversals across queries in one environment.
   The "assumptions-memo" debug flag reports each object whose traversal is
   replayed from an earlier query, so this file checks that the global
   environment stays physically the same across consecutive queries in
   batch mode, and that replays happen only when it does. *)

Axiom ax : nat.
Definition f := ax.
Definition g := f + 1.

Set Debug "assumptions-memo".

(* Nothing cached yet: no replay. *)
Print Assumptions g.
(* Same environment: [g] is replayed. *)
Print Assumptions g.
(* Sentences that do not declare anything keep the environment, as in the
   Checker's lemma pins, which interleave Set, Check and Print Assumptions. *)
Set Printing All. Check f. Unset Printing All.
(* [f] was walked by the first query. *)
Print Assumptions f.

Definition h := g.
(* A new constant changes the environment: everything is walked again. *)
Print Assumptions h.
Print Assumptions g.

Module M.
  (* Opening a module keeps the environment but changes the current module,
     which decides how sealed constants are looked up: the first query walks
     everything again, the second replays [g]. *)
  Print Assumptions g.
  Print Assumptions g.
End M.
