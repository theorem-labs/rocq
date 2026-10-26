(* A recursive occurrence in a PARAMETER of the head constructor. The
   cofixpoint analysis checked only the constructor's real arguments, so the
   parameter [f0 (hdN recur)], which destructs the cofixpoint, was checked by
   nothing, and `Eval cbv in hdN cycleQ` evaluates it on every unfolding.
   Typing accepts the term: [SN (f0 (hdN recur))] converts to [SN 0]. Found
   by the same-family review of this branch (BugFind93 bf93_01, Review93 r3).
   This branch's parent, and upstream's source at the v9.3 commit
   d91dbf084f, have the same Construct case, which skips the parameters.
   dispatch://BET-241 *)
CoInductive SN (n : nat) : Type := consN : SN n -> SN n.
Arguments consN {n} _.
Definition hdN {n : nat} (s : SN n) : SN n := match s with consN t => t end.
Definition f0 (s : SN 0) : nat := 0.

Fail Definition cycleQ : SN 0 :=
  cofix recur : SN 0 := @consN (f0 (hdN recur)) recur.
