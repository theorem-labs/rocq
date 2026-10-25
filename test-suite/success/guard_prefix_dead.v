(* Four definitions that carry an occurrence of the inner fixpoint in its
   BINDER PREFIX, where the reduction that prepares the body for the
   uniform-parameter analysis erases it. They are accepted here, and they are
   refused by the 9.2 release, by stock Rocq 9.2.0 and by stock 9.3+rc1
   (binary-equivalence-taiga, dispatch://BET-214, 2026-10-25).

   Why the earlier toolchains refuse them, and why that is not a soundness
   judgment about the definitions. The analysis measures the body after its
   leading abstractions are stripped and reduced; the pass that rewrites the
   body for the extruded fixpoint used to walk the body as written. The two
   therefore disagreed about any occurrence that only exists before the
   reduction: upstream raises Failure "List.skipn" there, the release drops
   fewer arguments than it meant to and the later guard check rejects the
   rewritten term, and an earlier head of this branch refused on sight. This
   branch gives both passes the same stripped body, so there is no
   disagreement to resolve and these definitions are judged on what the
   kernel actually runs.

   Why the erased occurrence cannot be reached at run time. In each case the
   occurrence sits in a binder-prefix position that the kernel's own
   reduction removes before the body can be applied: a local definition whose
   value is never forced on a reachable path (the first two), an argument of a
   beta redex that is discarded by the function it is passed to (the third),
   and a branch selected on a constructor that is already decided (the
   fourth). Evaluation never reaches a state in which that occurrence is the
   head, so the recursion that remains at run time is the one the guard
   condition checked: the inner loop descends on its own structural argument
   and the outer call is made on a strict subterm. The computations below
   exercise each definition on concrete inputs and are checked by conversion,
   so a non-terminating one would not compile. *)

(* a local definition in the prefix, holding the inner fixpoint unapplied *)
Definition outerX1a : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := inner).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Defined.

Example outerX1a_0 : outerX1a 0 = 0 := eq_refl.
Example outerX1a_5 : outerX1a 5 = 0 := eq_refl.

(* the same, with the prefix binding used by the body *)
Definition outerX1live : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (live := inner).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (live a k).
Defined.

Example outerX1live_0 : outerX1live 0 = 0 := eq_refl.
Example outerX1live_7 : outerX1live 7 = 0 := eq_refl.

(* the occurrence partially applied *)
Definition outerX2 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat -> nat) p p p).
    fix inner 3.
    pose (dead := inner O).
    intros a b m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a b k).
Defined.

Example outerX2_0 : outerX2 0 = 0 := eq_refl.
Example outerX2_4 : outerX2 4 = 0 := eq_refl.

(* a dead beta argument instead of a local definition *)
Definition outerX4 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine ((fun _ : nat -> nat -> nat => _) inner).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Defined.

Example outerX4_0 : outerX4 0 = 0 := eq_refl.
Example outerX4_6 : outerX4 6 = 0 := eq_refl.

(* The same shapes without the prefix occurrence, as the control: these are
   accepted by every toolchain, so a run that rejects the four above and this
   one too is rejecting the shape rather than the erased occurrence. *)
Definition outerX0 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Defined.

Example outerX0_3 : outerX0 3 = 0 := eq_refl.
