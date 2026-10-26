(* A match with case inversion (Definitional UIP, an SProp equality, one
   branch without binders) on a VARIABLE scrutinee, at the HEAD of an
   application. [whd_all] inverts it to the branch [fun _ y => consB y],
   beta-reduces and DROPS the argument [hdB recur], which destructs the
   cofixpoint. The walk in [check_one_cofix] reduces such a match with
   [whd_all] once it holds no recursive occurrence, and then sees the
   dropped argument. The pattern writes the constructor's explicit parameter
   ("srefl _", as test-suite/success/sprop_uip.v:23 does): with a bare
   "srefl" the file is refused by elaboration on every build, and the Fail
   below then succeeds for a reason that is not the guard. Found by the
   same-family review of this branch (Review93, r1); dispatch://BET-241. *)
Set Definitional UIP.
Inductive seq {A : Type} (a : A) : A -> SProp := srefl : seq a a.
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.

Fail Definition cycU (h : seq 0 0) : SB :=
  cofix recur : SB :=
    (match h in seq _ k return SB -> SB -> SB with
     | srefl _ => fun (_ y : SB) => consB y end) (hdB recur) recur.
