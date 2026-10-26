(* The erased position a field that a primitive projection of a known record
   does not select. It destructs the cofixpoint. Accepted by the 9.2
   release-7 cut 18da2c8ff497 and by this branch's 9.3 parent, each with
   "Closed under the global context" and `coqchk -o -norec` exit 0, while
   `Eval cbv in (hdB (hdB cycleP))` dies with "Error: Stack overflow".
   (q3 of dispatch://BET-241.) *)
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.
Set Primitive Projections.
Record PP : Type := mkPP { pp1 : SB ; pp2 : SB }.
Unset Primitive Projections.

Fail Definition cycleP : SB :=
  cofix recur : SB := pp1 (mkPP (consB recur) (hdB recur)).
