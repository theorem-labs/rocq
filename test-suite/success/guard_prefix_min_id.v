(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* A terminating fixpoint whose recursive binder appears only after a
   constant is unfolded (delta, then beta). Stock 9.2.0 and upstream master
   accept it; the raw-prefix rule refused it with "Not enough abstractions
   in the definition" until it took head-reduction steps. Native
   compilation is off: the native compiler cannot compile such a body
   (rocq-prover/rocq#16599). *)
(* From rocq-prover/rocq#21136: the body has no syntactic binder; the
   recursive argument appears when [id] is unfolded. *)
Fixpoint foo : nat -> nat := id (fun n => match n with S n => foo n | O => O end).
