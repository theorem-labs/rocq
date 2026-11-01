(* The erased position a let inside the HEAD of an application, dropped
   while the head is reduced to the abstraction the argument is substituted
   into. It destructs the cofixpoint. The 9.2 release-7 cut 18da2c8ff497
   (whose cofixpoint rule reduces the head with [whd_all] and does not look
   at what that drops) accepts it with "Closed under the global context"
   and `coqchk -o -norec` exit 0, and `Eval cbv in (hdB (hdB cycleH))` dies
   with "Error: Stack overflow" (q2 of dispatch://BET-241). Ported from
   9.3/guard-cofix-prefix cc0d0871ad63. *)
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.

Fail Definition cycleH : SB :=
  cofix recur : SB := (let d := hdB recur in fun x : SB => consB x) recur.
