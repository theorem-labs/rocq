(* An erased beta argument of ANOTHER inductive type that mentions the
   cofixpoint without forcing it: [f_nat] ignores its argument, so the
   definition terminates. The 9.2 release-7 cut 18da2c8ff497 dies on it
   with Anomaly "Uncaught exception Invalid_argument("index out of
   bounds")", because its rule submits the dropped [S (f_nat recur)] to the
   cofixpoint analysis with the recursion tree of [SB]. The rule here does
   not use a tree for dropped material: it refuses any dropped term that
   mentions the block, so this definition is refused with an ordinary guard
   error. That refusal is the accepted cost of the rule; an anomaly would be
   a defect. [Fail] does not catch an anomaly, so this file fails on a
   kernel that raises one (q4 of dispatch://BET-241). Ported from
   9.3/guard-cofix-prefix cc0d0871ad63. *)
CoInductive SB : Type := consB : SB -> SB.
Definition f_nat (s : SB) : nat := 0.

Fail Definition cycleN : SB :=
  cofix recur : SB := (fun _ : nat => consB recur) (S (f_nat recur)).
