(* cold runs probe (flag inlined) on a cold VM cache; the Eval then fills the
   cache with probe2, and warm runs it from the cache. Nothing either reads
   changes, so both replay. *)
Require Import PR.A.

Lemma cold : True.
Proof.
  let b := eval vm_compute in (probe tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.

Eval vm_compute in (probe2 tt).

Lemma warm : True.
Proof.
  let b := eval vm_compute in (probe2 tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.
