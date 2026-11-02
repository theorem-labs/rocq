(* zify_iter_specs reads zify's process-wide copy of the spec table, which the
   last init_cache filled. [warm] fills it after the spec of my_min1 is
   registered; the edited tree registers the spec of my_min2 there instead.
   [warm] reads the changed table, so it runs its tactics in both compiles.
   [later] is unchanged and reads nothing else that changed, but in the
   edited tree the copy holds no spec for my_min1, so the stock script fails.
   Replay must fail too (breadth audit gap BA4). *)
From Stdlib Require Import ZArith ZifyClasses ZifyInst Zify.
Open Scope Z_scope.

Definition my_min1 (x y : Z) := Z.min x y.
Definition my_min2 (x y : Z) := Z.min x y.

#[global] Instance Spec1 : BinOpSpec my_min1 :=
  { BPred := fun x y r => r <= x ; BSpec := fun x y => Z.le_min_l x y }.
#[global] Instance Spec2 : BinOpSpec my_min2 :=
  { BPred := fun x y r => r <= x ; BSpec := fun x y => Z.le_min_l x y }.

Add Zify BinOpSpec Spec2.

Lemma warm (x : Z) : x = x.
Proof. zify_op. exact eq_refl. Qed.

Lemma later (x y : Z) (H : my_min1 x y = my_min1 x y) : True.
Proof.
  zify_iter_specs.
  lazymatch goal with
  | H : context [my_min1] |- _ => fail "zify_iter_specs posed no spec"
  | _ => exact I
  end.
Qed.
