(* p is the kernel's primitive int63 type, and target types a raw int63
   literal: the kernel takes the literal's type from its registry of
   primitive types, not from a lookup of p. The edited tree makes p the
   float64 type instead, so no int63 type is registered and stock fails to
   type the literal; target's key and every read it makes are unchanged.
   Replay must fail too (cross-model soundness review of 777213df6e,
   finding 2). *)
From Ltac2 Require Import Ltac2.

Primitive p := #float64_type.

Lemma target : True.
Proof.
  let _ := Constr.type (Constr.Unsafe.make (Constr.Unsafe.Uint63 (Uint63.of_int 0))) in
  exact I.
Qed.
