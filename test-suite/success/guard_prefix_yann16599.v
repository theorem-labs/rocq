(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* A terminating fixpoint whose recursive binder appears only after a
   constant is unfolded (delta, then beta). Stock 9.2.0 and upstream master
   accept it; the raw-prefix rule refused it with "Not enough abstractions
   in the definition" until it took head-reduction steps. Native
   compilation is off: the native compiler cannot compile such a body
   (rocq-prover/rocq#16599). *)
(* From rocq-prover/rocq#16599 (the 2026-01-21 minimisation): the
   recursive binder appears when [id] is unfolded. *)
Inductive Rec := { unrec : Rec }.

Definition f : Rec -> False.
Proof.
  fix rec 1.
  apply id.
  exact (fun x => rec (unrec x)).
Defined.
