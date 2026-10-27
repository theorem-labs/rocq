(* The dead-branch rule 958e3aab1c added to [check_one_cofix] refused any
   term the head reduction drops that mentions a function of the block, even a
   guarded occurrence that no reduction can force. That refused valid
   cofixpoints and, inside a module functor, split coqc from coqchk.

   test-suite/success runs [coqchk] on the .vo this file compiles, so every
   definition below pins coqc AND coqchk. On the 958e3aab1c rule:
     - [r50] and [cycM] are refused by coqc (q: BET-241, "Recursive
       definition of r50 is ill-formed");
     - [Inst.r] and [InstL.r] pass coqc and are refused by coqchk with
       IllFormedRecBody (exit 129): in the functor the match on the opaque
       [X.sel] is stuck, so the live guard checks both branches and accepts,
       and in the instance the match selects, the unselected branch becomes
       dropped material that mentions the block.
   Stock Rocq 9.2.0 accepts them all with a clean coqchk; so must we. *)

CoInductive St : Type := c : St -> St.
Definition hdS (s : St) : St := match s with c t => t end.

(* The dead branch written directly: [false] selects [c (c r50)], and the
   dropped [true] branch [c r50] is a guarded occurrence whose head is the
   constructor [c], which no reduction forces. *)
CoFixpoint r50 : St := match false with true => c r50 | false => c (c r50) end.
Print Assumptions r50.

(* The same under an applicator that drops its argument: [r] is dropped bare. *)
CoFixpoint cycA : St := (fun _ : St => c cycA) cycA.
Print Assumptions cycA.

(* The functor instance: the coqc/coqchk split. *)
Module Type PT. Parameter sel : bool. End PT.
Module Mk (X : PT).
  CoFixpoint r : St := match X.sel with true => c r | false => c (c r) end.
  Definition force : St := hdS r.
End Mk.
Module Arg <: PT. Definition sel := false. End Arg.
Module Inst := Mk Arg.
Print Assumptions Inst.r.

(* The dead value of a let, specialised from a functor parameter: inside the
   functor the binder is read through the match, after instantiation the match
   collapses and the binder goes unread, so [c r] is dropped. *)
Module MkL (X : PT).
  CoFixpoint r : St := let d := c r in match X.sel with true => d | false => c (c r) end.
End MkL.
Module InstL := MkL Arg.
Print Assumptions InstL.r.

(* A dropped branch reached through an [S]-guarded match on a known nat. *)
CoInductive SM : Type := consM : SM -> SM.
Definition hdM (s : SM) : SM := match s with consM t => t end.
CoFixpoint cycM : SM := match 0 with 0 => consM cycM | S _ => consM (consM cycM) end.
Print Assumptions cycM.

(* The field a primitive projection of a known record does not select is
   dropped (the :proj relaxed site). [pp1 (mkPP rP (c rP))] = rP, and the
   unselected field [c rP] is inert. *)
Set Primitive Projections.
Record PP : Type := mkPP { pp1 : St ; pp2 : St }.
Unset Primitive Projections.
CoFixpoint rP : St := c (pp1 (mkPP rP (c rP))).
Print Assumptions rP.

(* The constructor argument the selected branch does not read is dropped (the
   unread-argument relaxed site): [b] binds the second argument, the first
   [c rU] is unread and dropped. *)
Inductive two : Type := mkp : St -> St -> two.
CoFixpoint rU : St := match mkp (c rU) rU with mkp _ b => c b end.
Print Assumptions rU.

(* A constructor PARAMETER the match drops (the parameter relaxed site). The
   scrutinee's parameter is convertible to but not syntactically the return
   predicate's instance [tt], so the block occurs only in the dropped
   parameter [(fun _ => tt) rC]. *)
Inductive tag (u : unit) : Type := mktag : tag u.
Definition mk0 (s : St) : tag tt := mktag ((fun _ : St => tt) s).
CoFixpoint rC : St := match mk0 rC with mktag _ => c rC end.
Print Assumptions rC.

(* A dropped value that COMPUTES AWAY the block occurrence: [ignore_st]
   ignores its first argument, so the dropped [ignore_st (stream n) n] reduces
   to the parameter [n], a head the walk follows to a block-free normal form. *)
Definition ignore_st (s : St) (m : nat) : nat := m.
CoFixpoint stream (n : nat) : St := (fun _ : nat => c (stream n)) (ignore_st (stream n) n).
Print Assumptions stream.

(* Two cost-regression canaries pin the memo in [dropped]. The dropped term
   duplicates a sub-term per level, so a walk that re-reduces each copy is
   exponential in [depth]. The memo keys on structural equality at each depth
   (not physical identity) and re-reads its depth bucket after [inert] returns
   (not a pre-[inert] snapshot), so each distinct sub-term is examined once and
   both compile instantly; without either half of the memo they do not
   terminate. Both definitions are valid (the live [false] branch is just
   [c r*]); stock accepts them in O(depth). *)
Inductive Pair2 : Type := pr2 : St -> St -> Pair2.

(* Canary A: subst-shared duplication [pr2 s s]. Catches a regression that
   loses the memo entirely. *)
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

(* Canary B: a wrapped source-duplicated copy [pr2 (c (f s)) (c (f s))].
   The two [c (f s)] are two separate [App] nodes, not shared by [subst], so a
   physical-only memo misses them, and the wrapping [c _] descends through a
   nested [dropped] call that would clobber a stale-snapshot write. Catches
   both: a memo that only compares with [==], and a memo that writes with the
   pre-[inert] bucket. *)
Definition dupB (f : St -> St) : St -> St :=
  fun s => match pr2 (c (f s)) (c (f s)) with pr2 a _ => c a end.
Definition qB0 : St -> St := fun s => s.
Definition qB1 : St -> St := dupB qB0.
Definition qB2 : St -> St := dupB qB1.
Definition qB3 : St -> St := dupB qB2.
Definition qB4 : St -> St := dupB qB3.
Definition qB5 : St -> St := dupB qB4.
Definition qB6 : St -> St := dupB qB5.
Definition qB7 : St -> St := dupB qB6.
CoFixpoint rBlowB : St := match false with true => qB7 (qB6 rBlowB) | false => c rBlowB end.
Print Assumptions rBlowB.
