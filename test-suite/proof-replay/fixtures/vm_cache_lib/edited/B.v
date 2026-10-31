(* The Eval fills the VM cache with probe's value before target opens, so
   target's vm_compute finds probe in the cache and never looks flag up.
   With the edited A, stock rejects target, so replay must too. *)
Require Import PR.A.

Eval vm_compute in (probe tt).

Lemma target : True.
Proof.
  let b := eval vm_compute in (probe tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.
