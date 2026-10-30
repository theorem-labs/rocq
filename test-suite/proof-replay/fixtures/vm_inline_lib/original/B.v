(* target runs probe's bytecode, which holds flag's value, and never looks
   flag up. With the edited A, stock rejects target, so replay must too. *)
Require Import PR.A.

Lemma target : True.
Proof.
  let b := eval vm_compute in (probe tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.
