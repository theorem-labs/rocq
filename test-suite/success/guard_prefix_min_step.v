(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* A terminating fixpoint whose recursive binder appears only after a
   constant is unfolded (delta, then beta). Stock 9.2.0 and upstream master
   accept it; the raw-prefix rule refused it with "Not enough abstractions
   in the definition" until it took head-reduction steps. Native
   compilation is off: the native compiler cannot compile such a body
   (rocq-prover/rocq#16599). *)
(* The recursive argument is the second argument, but the body has one
   syntactic binder; the second appears when [step] is unfolded. *)
Definition step (g : nat -> nat) : nat -> nat :=
  fun m => match m with O => O | S k => g k end.

Definition inner : nat -> nat -> nat.
Proof. fix rec 2. intros a. exact (step (rec a)). Defined.
