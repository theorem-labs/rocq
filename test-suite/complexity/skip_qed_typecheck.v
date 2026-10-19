(* coq-prog-args: ("-skip-qed-typecheck") *)
(* With -skip-qed-typecheck, Qed does not run the kernel's typechecking of
   the proof, which here is a vm_compute of 2^27 boolean negations (about 4s
   without the option). *)
(* Expected time < 0.50s *)

Fixpoint pow2 (n : nat) (b : bool) : bool :=
  match n with O => negb b | S n => pow2 n (pow2 n b) end.

Lemma big : pow2 27 true = true.
Proof.
vm_cast_no_check (eq_refl true).
Time Qed.
