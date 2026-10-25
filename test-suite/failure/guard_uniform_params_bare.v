(* A terminating definition that this toolchain REFUSES, where Rocq 9.2.0,
   Rocq 9.3.0 and upstream master DIE with
   Anomaly "Uncaught exception Failure("List.skipn")"
   (measured 2026-10-25, binary-equivalence-taiga, dispatch://BET-214).

   The inner fixpoint [inner] is handed to the let-bound [invoke] without being
   applied. The uniform-parameter analysis folds over the arguments of a
   recursive call with [fold_constr_with_binders], which visits the immediate
   children of each argument; a bare occurrence is a [Rel] and has none, so the
   occurrence was never seen and the analysis kept believing that a prefix of
   [inner]'s arguments is uniform. The rewriting pass then met that same bare
   occurrence, applied to nothing, and asked [List.skipn] to drop a positive
   number of arguments from an empty list.

   An unapplied occurrence lets no prefix be extruded, so the analysis now
   reports a uniform prefix of 0 for it. That is what [List.skipn] needs to be
   total here. The price is that this definition is refused rather than
   accepted: without an extruded prefix, the analysis can no longer see that
   [a] keeps the value [p], so the call [outer a] is not recognised as
   decreasing. A development that needs this shape applies the inner fixpoint
   directly, [inner a k], instead of passing it through [invoke].

   This only changes definitions on which the released toolchains raise that
   anomaly; where they return an answer, this analysis returns the same one. *)

Fail Fixpoint outer (n : nat) : nat :=
  match n with
  | O => O
  | S p =>
      let invoke := fun (h : nat -> nat -> nat) (a m : nat) => h a m in
      (fix inner (a m : nat) {struct m} : nat :=
         match m with
         | O => outer a
         | S k => invoke inner a k
         end) p p
  end.
