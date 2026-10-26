(* The co-recursive form of the binder-prefix defect. [check_one_cofix]
   analyses [whd_all] of the body, the kernel stores the body as written,
   so the argument of this beta redex — whose binder the body never reads —
   is checked by nothing. It holds a destruction of the cofixpoint itself,
   which the analysis would refuse in a position it measures.

   Accepted by the 9.2 release febc57ac52, by the cut d9061a3408, by stock
   Rocq 9.2.0, 9.3+rc1 and 9.4+alpha, and by this branch's 9.3 parent
   (9.3/guard-uniform-bounds 30a1b2bbefca), each with "Closed under the
   global context" and `coqchk -o -norec` exit 0, while
   `Eval cbv in (hdB cycleB)` dies with "Error: Stack overflow". *)
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.

Fail Definition cycleB : SB :=
  cofix recur : SB := (fun _ : SB => consB recur) (hdB recur).
