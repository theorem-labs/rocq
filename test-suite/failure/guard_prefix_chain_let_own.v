(* Red on the release-7 rule: accepted with coqchk 0. Stock Rocq 9.0.1 refuses
   this file too, but for the inner body's call "outer a", not for the call in
   the prefix. The inner block's own check_fix now substitutes the live let and
   sees "inner O (S O)" in the dead one. dispatch://BET-214 *)
(* Nested fixpoint calling ITSELF on a constructor argument from its own
   prefix, through a let read only by a second, dead let. The inner block's
   own check_fix (raw_prefix_escapes) sees "Rel 1" in the dead value. *)
Definition outer_own_chain : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (x := inner O (S O)).
    pose (y := x).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Fail Defined.
Abort.
