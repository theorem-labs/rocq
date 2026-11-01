(* The SCRUTINEE of an ordinary match is a match with case inversion on a
   variable. [whd_all] inverts the inner match to [true], takes iota on the
   outer match and DROPS the [false] branch, which destructs the
   cofixpoint; refused for the same reason as guard_cofix_dead_match.v. The
   9.2 release-7 cut 18da2c8ff497 refuses this file's definition too; the
   file guards the walk's case-inversion path. The inner pattern writes the
   constructor's explicit parameter ("srefl _", as
   test-suite/success/sprop_uip.v does): with a bare "srefl" the definition
   is refused by elaboration, and the Fail below would then succeed for a
   reason that is not the guard. Ported from 9.3/guard-cofix-prefix
   cc0d0871ad63. dispatch://BET-241 *)
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
