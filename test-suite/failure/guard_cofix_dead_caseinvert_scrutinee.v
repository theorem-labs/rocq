(* The SCRUTINEE of an ordinary match is a match with case inversion on a
   variable. [whd_all] inverts the inner match to [true], takes iota on the
   outer match and DROPS the [false] branch, which destructs the
   cofixpoint; refused for the same reason as guard_cofix_dead_match.v. The
   inner pattern writes the constructor's explicit parameter ("srefl _", as
   test-suite/success/sprop_uip.v:23 does): with a bare "srefl" the file is
   refused by elaboration on every build, and the Fail below then succeeds
   for a reason that is not the guard. Found by the same-family review of
   this branch (Review93, r2); dispatch://BET-241. *)
Set Definitional UIP.
Inductive seq {A : Type} (a : A) : A -> SProp := srefl : seq a a.
CoInductive SB : Type := consB : SB -> SB.
Definition hdB (s : SB) : SB := match s with consB t => t end.

Fail Definition cycV (h : seq 0 0) : SB :=
  cofix recur : SB :=
    match (match h in seq _ k return bool with srefl _ => true end) with
    | true => consB recur
    | false => hdB recur
    end.
