(* The five fully applied prefix calls of guard_prefix_attack_*.v in one
   file, with the reasoning that makes them unsound written out. Each one
   must be refused, and this branch refuses all five.

   Each puts a FULLY APPLIED recursive call of the inner fixpoint in that
   fixpoint's binder prefix, where the reduction that prepares the body for
   the uniform-parameter analysis erases it: a local definition, a nested
   local definition, a discarded beta argument, a cast, and a branch of a
   match that is already decided. The analysis therefore measures its prefix
   from the applied occurrence in the body proper, while the stored body
   still carries [inner O (S O)] in the binder prefix, which nothing checked.

   That occurrence is a real call, not one evaluation can never reach: with
   the extruded prefix the guard check no longer sees the argument that was
   dropped, the outer call passes as decreasing, and the constant diverges.
   On a build that truncates instead of refusing, each of the five compiles
   with "Closed under the global context" and a clean coqchk -o, and [cbv]
   on the result reports Stack overflow (measured 2026-10-25,
   binary-equivalence-taiga, dispatch://BET-214, on this branch's own 9.0 and
   9.2 heads before the raw-prefix rule; the match variant evaluates to 0
   because its erased branch is not the one taken). Rocq 9.0.1 refuses all
   five, for the unrelated reason that it lacks rocq-prover/rocq#22384.

   The rule that refuses them scans each body's RAW binder prefix before any
   reduction runs and refuses the definition if it mentions any function of
   the block. An occurrence there that is BARE or PARTIALLY APPLIED is
   harmless in itself, but it is refused by the same rule, because telling
   the two apart would need the reduction that erases them:
   guard_uniform_params_dead.v holds that family. *)

(* a local definition in the prefix holding a fully applied call *)
Definition outer_bad_let : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := inner O (S O)).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.

(* the same call, one local definition deeper *)
Definition outer_bad_nested_let : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := let also_dead := inner O (S O) in also_dead).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.

(* a beta redex whose argument is the fully applied call and is discarded *)
Definition outer_bad_beta : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine ((fun _ : nat => _) (inner O (S O))).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.

(* the call carried by a cast that the reduction removes *)
Definition outer_bad_cast : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (@eq_rect nat (inner O (S O)) (fun _ => nat -> nat -> nat) _ (inner O (S O)) eq_refl).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.

(* the call in the branch of a match on a constructor that is already decided *)
Definition outer_bad_match : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (match O with O => _ | S _ => fun _ _ => inner O (S O) end).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.
