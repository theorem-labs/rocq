(* A prefix whose material the reduction KEEPS is not erased material: the
   reduction substitutes it into the body the analysis measures, so the
   analysis sees the recursive call and the rule must stay out of the way.
   Both shapes are ordinary ways to write a fixpoint proof, and the 9.2
   release accepts both. *)

(* Naming the induction hypothesis: "pose proof inner as IH" puts a let in
   the prefix whose value is the inner fixpoint and whose binder the body
   reads. *)
Definition prefix_pose_proof : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose proof inner as IH.
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (IH a k).
Defined.

Print Assumptions prefix_pose_proof.
Example prefix_pose_proof_computes : prefix_pose_proof 5 = 0 := eq_refl.

(* The prefix is a beta redex whose argument is the inner fixpoint and whose
   binder the body reads. *)
Definition prefix_beta_applier : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat -> nat) p p p).
    fix inner 3.
    refine ((fun (g : nat -> nat -> nat -> nat) => _) inner).
    intros a b m.
    destruct m as [|k].
    + exact (outer p).
    + exact (g a b k).
Defined.

Print Assumptions prefix_beta_applier.
Example prefix_beta_applier_computes : prefix_beta_applier 5 = 0 := eq_refl.

(* The prefix binds the inner fixpoint itself and the body READS the binding.
   This one was in test-suite/failure/guard_uniform_params_dead.v as
   outerX1live, because the 9.2 release, stock 9.2.0 and stock 9.3+rc1 all
   refuse it: their analysis measures the stripped body while their rewriting
   walks the body as written, the two disagree about this occurrence, and the
   refusal is that disagreement rather than a property of the definition.
   This branch measures one term, so the disagreement is gone, and the
   definition is what it looks like: terminating. `Eval lazy`, `Eval vm_compute`
   and `Eval cbv` on `outerX1live 4` all return 0 (probe
   attacks-cofixprefix/x1live_eval.v). The three shapes beside it in that file,
   whose binding the body does NOT read, stay refused. *)
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

Print Assumptions outerX1live.
Example outerX1live_computes : outerX1live 4 = 0 := eq_refl.
