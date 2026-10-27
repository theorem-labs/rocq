(* An erased beta argument of another inductive type that mentions the
   cofixpoint without forcing it: [f_nat] ignores its argument, so the
   dropped [S (f_nat recur)] reduces to [S 0] and the definition terminates.

   The 958e3aab1c rule refused it ("refuses any dropped term that mentions the
   block"); this file was in test-suite/failure, documenting that refusal as a
   cost. The dropped-material rule now accepts it, because no occurrence of the
   block in the dropped term can be forced, so it is strongly normalising.
   Stock Rocq 9.2.0 accepts it with a clean coqchk, and [vm_compute]/[cbv]
   both terminate. (The 9.2 release-7 cut 18da2c8ff497, whose cofixpoint rule
   submitted the dropped term to the recursion tree of [SB], died on it with
   Anomaly "index out of bounds"; the dropped-material rule uses no tree, so it
   neither refuses nor crashes here.) Ported from 9.3/guard-cofix-prefix
   cc0d0871ad63. dispatch://BET-241 *)
CoInductive SB : Type := consB : SB -> SB.
Definition f_nat (s : SB) : nat := 0.
Definition hdB (s : SB) : SB := match s with consB t => t end.
Definition cycleN : SB :=
  cofix recur : SB := (fun _ : nat => consB recur) (S (f_nat recur)).
Print Assumptions cycleN.
Timeout 20 Eval vm_compute in (hdB (hdB cycleN)).
Timeout 20 Eval cbv in (hdB (hdB cycleN)).
