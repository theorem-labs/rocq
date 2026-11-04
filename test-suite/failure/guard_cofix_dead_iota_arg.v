(* The erased position a constructor argument that the selected branch of a
   match on a known constructor does not read: the substitution drops it.
   It destructs the cofixpoint. The 9.2 release-7 cut 18da2c8ff497 (whose
   cofixpoint rule does not walk into the scrutinee's arguments) accepts it
   with "Closed under the global context" and `coqchk -o -norec` exit 0,
   and `Eval cbv in (hdB (hdB cycleC))` dies with "Error: Stack overflow"
   (q1 of dispatch://BET-241). Ported from 9.3/guard-cofix-prefix
   cc0d0871ad63. *)
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.
Inductive Box : Type := box : SB -> Box.

Fail Definition cycleC : SB :=
  cofix recur : SB := match box (hdB recur) with box _ => consB recur end.
