(* An admitted model library reached from no checked library. The per-statement
   report must produce a verdict, not a kernel anomaly. Before the
   recheck_library admit-intern fix, an admitted library that is a dependency of
   no checked or norec library was never interned, so computing its closure
   raised Anomaly "missing dep when computing closure (StmtAdmit.Model)" and
   aborted the whole run. Found by S4 (BET-257), 2026-10-28. Built with -noinit
   so it depends on nothing. *)

Inductive mnat : Set := mO : mnat | mS : forall _ : mnat, mnat.
Axiom max : mnat.
Definition m : mnat := max.
