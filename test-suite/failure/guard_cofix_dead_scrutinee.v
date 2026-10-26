(* The erased position a beta argument inside the SCRUTINEE of a match,
   dropped while the scrutinee is reduced to a constructor. It destructs the
   cofixpoint. Accepted by the 9.2 release-7 cut 18da2c8ff497 and by this
   branch's 9.3 parent, each with "Closed under the global context" and
   `coqchk -o -norec` exit 0, while `Eval cbv in (hdB (hdB cycleS))` dies
   with "Error: Stack overflow". (q5 of dispatch://BET-241.) *)
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.
Inductive Box : Type := box : SB -> Box.

Fail Definition cycleS : SB :=
  cofix recur : SB :=
    match (fun _ : SB => box recur) (hdB recur) with box s => consB s end.
