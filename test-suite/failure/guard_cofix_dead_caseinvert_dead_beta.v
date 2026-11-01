(* A match with case inversion (Definitional UIP, an SProp equality, one
   branch without binders) on a VARIABLE scrutinee, at the HEAD of an
   application. [whd_all] inverts it to the branch [fun _ y => consB y],
   beta-reduces and DROPS the argument [hdB recur], which destructs the
   cofixpoint. The walk in [check_one_cofix] does not take case inversion
   apart: it refuses such a match when it mentions the block, and otherwise
   continues from [whd_all] of it. The 9.2 release-7 cut 18da2c8ff497
   refuses this file's definition too (its rule reduces the head with
   [whd_all]); the file guards the walk's case-inversion path. The pattern
   writes the constructor's explicit parameter ("srefl _", as
   test-suite/success/sprop_uip.v does): with a bare "srefl" the definition
   is refused by elaboration, and the Fail below would then succeed for a
   reason that is not the guard. Ported from 9.3/guard-cofix-prefix
   cc0d0871ad63. dispatch://BET-241 *)
Set Definitional UIP.
Inductive seq {A : Type} (a : A) : A -> SProp := srefl : seq a a.
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.

Fail Definition cycU (h : seq 0 0) : SB :=
  cofix recur : SB :=
    (match h in seq _ k return SB -> SB -> SB with
     | srefl _ => fun (_ y : SB) => consB y end) (hdB recur) recur.
