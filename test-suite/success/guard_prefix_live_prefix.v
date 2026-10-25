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
