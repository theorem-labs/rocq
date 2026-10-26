(* A branch dropped by a match whose scrutinee reduces only through a
   PRIMITIVE operation ([eqb 0 0] reduces to [true]). [whd_all] takes that
   step and drops the [false] branch, which destructs the cofixpoint. The
   walk in [check_one_cofix] does not take a primitive apart: it reduces
   such a scrutinee with [whd_all] once it holds no recursive occurrence,
   and then sees the dropped branch. The 9.2 release-7 cut 18da2c8ff497
   refuses this file's definition too; the file guards the walk's primitive
   path. Ported from 9.3/guard-cofix-prefix cc0d0871ad63.
   dispatch://BET-241 *)
From Corelib Require Import PrimInt63.
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.

Fail Definition cycleI : SB :=
  cofix recur : SB :=
    match eqb 0%uint63 0%uint63 with true => consB recur | false => hdB recur end.
