(* The erased position a beta argument inside the SCRUTINEE of a match,
   dropped while the scrutinee is reduced to a constructor. It destructs the
   cofixpoint. The 9.2 release-7 cut 18da2c8ff497 accepts it with "Closed
   under the global context" and `coqchk -o -norec` exit 0, and
   `Eval cbv in (hdB (hdB cycleS))` dies with "Error: Stack overflow" (q5 of
   dispatch://BET-241). Ported from 9.3/guard-cofix-prefix cc0d0871ad63. *)
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.
Inductive Box : Type := box : SB -> Box.

Fail Definition cycleS : SB :=
  cofix recur : SB :=
    match (fun _ : SB => box recur) (hdB recur) with box s => consB s end.
