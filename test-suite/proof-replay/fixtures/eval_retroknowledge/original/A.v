(* Both proofs type a raw int63 literal, whose type the kernel takes from its
   registry of primitive types (retroknowledge), not from a lookup of a
   constant. The edited tree registers one more primitive type between the
   two proofs: [changed] must miss on the retroknowledge read, and [same],
   which starts before it, must replay. *)
From Ltac2 Require Import Ltac2.

Primitive int := #int63_type.

Lemma same : True.
Proof. let _ := Constr.type (Constr.Unsafe.make (Constr.Unsafe.Uint63 (Uint63.of_int 0))) in exact I. Qed.

Lemma changed : True.
Proof. let _ := Constr.type (Constr.Unsafe.make (Constr.Unsafe.Uint63 (Uint63.of_int 0))) in exact I. Qed.
