(* A branch dropped by a match whose scrutinee reduces only through a
   PRIMITIVE operation ([eqb 0 0] reduces to [true]). [whd_all] takes that
   step and drops the [false] branch, which destructs the cofixpoint; the
   walk in [check_one_cofix] reduces such a scrutinee with [whd_all] once it
   holds no recursive occurrence, and then sees the dropped branch.
   (Port93, dispatch://BET-241.) *)
From Corelib Require Import PrimInt63.
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.

Fail Definition cycleI : SB :=
  cofix recur : SB :=
    match eqb 0%uint63 0%uint63 with true => consB recur | false => hdB recur end.
