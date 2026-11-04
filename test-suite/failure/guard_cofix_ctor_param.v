(* A recursive occurrence in a PARAMETER of the head constructor. The
   cofixpoint analysis checked only the constructor's real arguments, so the
   parameter [f0 (hdN recur)], which destructs the cofixpoint, was checked by
   nothing, and `Eval cbv in hdN cycleQ` evaluates it on every unfolding.
   Typing accepts the term: [SN (f0 (hdN recur))] converts to [SN 0]. The
   9.2 release-7 cut 18da2c8ff497 accepts it (this file fails there with
   "The command has not failed!"). Ported from the 9.3 member
   9.3/guard-cofix-prefix cc0d0871ad63. dispatch://BET-241 *)
CoInductive SN (n : nat) : Type := consN : SN n -> SN n.
Arguments consN {n} _.
Definition hdN {n : nat} (s : SN n) : SN n := match s with consN t => t end.
Definition f0 (s : SN 0) : nat := 0.

Fail Definition cycleQ : SN 0 :=
  cofix recur : SN 0 := @consN (f0 (hdN recur)) recur.
