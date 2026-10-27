(* The dead-material check at 958e3aab1c refused any dropped term that
   mentions the block, and so refused valid cofixpoints whose dead branch
   held a GUARDED occurrence (e.g. a constructor applied to the block).
   The dropped-material rule GuardDrop added at 2ddda3c4 exempted
   [cofix_inert] (the block at the head of its dropped term applied to
   block-free arguments), but still refused a dropped CONSTRUCTOR applied
   to the block, so a dropped [c r] stayed refused. In a module functor the
   match on the parameter is stuck, so the live guard checks every branch
   and coqc accepts; in the instance the match selects, the unselected
   branch becomes dropped material and coqchk refuses the compiled object.
   stock Rocq 9.2.0 accepts them all with coqchk 0; so must we.

   This file exercises every value-carrying dropped position the member
   relaxes from the strict rule: unselected match branches, dead let value,
   dead beta argument, plain unread constructor argument, dropped
   projection field. Positions iota can still FORCE stay with the strict
   rule and are checked in test-suite/failure/guard_cofix_dropped_forced.v. *)

CoInductive St : Type := c : St -> St.
Definition hdS (s : St) : St := match s with c t => t end.

(* Direct dead branch: [false] selects [c (c r50)], and [c r50] is dropped. *)
CoFixpoint r50 : St := match false with true => c r50 | false => c (c r50) end.
Print Assumptions r50.

(* Dropped applicator argument: [cycA] is a bare block occurrence dropped by
   a lambda whose binder is unused. *)
CoFixpoint cycA : St := (fun _ : St => c cycA) cycA.
Print Assumptions cycA.

(* The functor-instance split: coqc on the functor is stuck on [X.sel]; the
   instance reduces it, iota selects the [false] branch, and [c r] in the
   unselected branch becomes dropped material. *)
Module Type PT. Parameter sel : bool. End PT.
Module Mk (X : PT).
  CoFixpoint r : St := match X.sel with true => c r | false => c (c r) end.
  Definition force : St := hdS r.
End Mk.
Module Arg <: PT. Definition sel := false. End Arg.
Module Inst := Mk Arg.
Print Assumptions Inst.r.

(* The same with a dead LET value instead of a dead branch. *)
Module MkL (X : PT).
  CoFixpoint r : St := let d := c r in match X.sel with true => d | false => c (c r) end.
End MkL.
Module InstL := MkL Arg.
Print Assumptions InstL.r.

(* Dropped projection field: [pp1 (mkPP rP (c rP))] = rP, dropping [c rP]. *)
Set Primitive Projections.
Record PP : Type := mkPP { pp1 : St ; pp2 : St }.
Unset Primitive Projections.
CoFixpoint rP : St := c (pp1 (mkPP rP (c rP))).
Print Assumptions rP.

(* Unread constructor argument (no let-in in [two]): the match binds the
   second arg to [b], unread, so [c rU] is dropped. *)
Inductive two : Type := mkp : St -> St -> two.
CoFixpoint rU : St := match mkp (c rU) rU with mkp _ b => c b end.

(* GuardDrop recorded this as a cost (fork refuses, stock accepts). The
   dropped-material rule accepts it: [consL inside_ctor] is constructor-headed
   with an inert block argument that nothing in the dropped term forces. *)
CoInductive SL : Type := consL : SL -> SL.
CoFixpoint inside_ctor : SL := let dead := consL inside_ctor in consL inside_ctor.
Print Assumptions inside_ctor.
Print Assumptions rU.

(* A dropped value that computes the block occurrence away: [ignore_st]
   ignores its first argument, so the dropped [ignore_st (stream n) n]
   reduces to [n], a non-block Rel the walk's stuck-head catch-all accepts
   because the whnf is block-free. *)
Definition ignore_st (s : St) (m : nat) : nat := m.
CoFixpoint stream (n : nat) : St := (fun _ : nat => c (stream n)) (ignore_st (stream n) n).
Print Assumptions stream.

(* A memo canary: the dropped term duplicates a sub-term per level, which
   [subst] shares physically. [dropped]'s per-depth physical-identity memo
   collapses the duplication to linear; without the memo this does not
   terminate at this depth. The definition is valid; stock accepts in O(depth). *)
Inductive Pair2 : Type := pr2 : St -> St -> Pair2.
Definition dupS (s : St) : St := match pr2 s s with pr2 a _ => c a end.
Definition qA0 (s : St) : St := dupS s.
Definition qA1 (s : St) : St := qA0 (qA0 s).
Definition qA2 (s : St) : St := qA1 (qA1 s).
Definition qA3 (s : St) : St := qA2 (qA2 s).
Definition qA4 (s : St) : St := qA3 (qA3 s).
Definition qA5 (s : St) : St := qA4 (qA4 s).
Definition qA6 (s : St) : St := qA5 (qA5 s).
Definition qA7 (s : St) : St := qA6 (qA6 s).
CoFixpoint rBlowA : St := match false with true => qA7 (qA6 rBlowA) | false => c rBlowA end.
Print Assumptions rBlowA.
