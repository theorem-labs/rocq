(*
   Three definitions that must be refused, and are refused by Rocq 9.2.0 and
   Rocq 9.3+rc1 with an ordinary "ill-formed" diagnostic. Found by the review
   of this branch (binary-equivalence-taiga, dispatch://BET-214, 2026-10-25).

   Each carries an occurrence of the inner fixpoint in the BINDER PREFIX of
   that fixpoint, where the uniform-parameter analysis cannot see it and the
   rewriting pass can. The analysis runs on the body after the prefix has been
   stripped and reduced; the rewriting pass walks the body as written, meets
   the occurrence, and is asked to drop a prefix of arguments that the
   occurrence does not have.

   Upstream raises Failure "List.skipn" from the kernel there; the 9.2 base
   silently dropped what it could, which accepts the rewritten body on an
   assumption nothing checked. This branch refuses the definition instead.

   A FOURTH definition used to be here, outerX1live, whose prefix binding the
   body READS. It now lives in test-suite/success/guard_prefix_live_prefix.v:
   the reduction substitutes a read binding into the body the analysis
   measures, so the analysis sees the recursive call and judges it, and the
   definition terminates — `Eval lazy`, `Eval vm_compute` and `Eval cbv` on
   `outerX1live 4` all return 0. The release refuses it only because its two
   passes disagree about the term, and this branch removed that disagreement.

   This file passes before this branch as well as after: the 9.2 release
   refuses these three too. It pins that we keep matching the release, and it
   caught the head where we did not, which raised the anomaly on all four. *)



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
  Fail Defined.
Abort.

(* the same, with the occurrence partially applied *)
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
  Fail Defined.
Abort.

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
  Fail Defined.
Abort.
