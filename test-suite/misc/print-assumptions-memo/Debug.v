(* Print Assumptions reuses traversals across queries in one environment.
   With ROCQ_DEBUG_ASSUMPTIONS_MEMO=1 each replay of an earlier query's
   traversal is reported on standard error, so this file checks that the
   global environment stays physically the same across consecutive queries in
   batch mode, and that replays happen only when it does. *)

Axiom ax : nat.
Definition f := ax.
Definition g := f + 1.

(* Nothing cached yet: no replay. *)
Print Assumptions g.
(* Same environment: [g] is replayed. *)
Print Assumptions g.
(* Sentences that do not declare anything, such as Set, Check and Unset,
   keep the environment. *)
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

(* With every debug flag on, the replay notice still goes only to standard
   error: the script checks that standard output is the same with and without
   ROCQ_DEBUG_ASSUMPTIONS_MEMO. "-misc" because that flag makes the document
   manager run the external program dot. Closing [M] changed the environment:
   the first query walks, the second replays [g]. *)
Set Debug "all,-misc".
Print Assumptions g.
Print Assumptions g.
