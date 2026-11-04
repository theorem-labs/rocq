(* The same short names in two modules. Import changes which constant a short
   name denotes without adding anything to the global environment, so the
   entries recorded before it stay while the queries after it ask about other
   objects.

   The (*NOREUSE*) marks are where the control arm of
   print-assumptions-memo-stale.sh puts a definition of its own, which
   changes the environment and so leaves every query a walk without reuse. *)

Axiom ax1 : nat.
Axiom ax2 : nat.

Module M1.
  Definition f : nat := ax1.
  Definition g : nat := f.
End M1.

Module M2.
  Definition f : nat := ax2.
  Definition g : nat := f.
End M2.

(*NOREUSE*) Print Assumptions M1.g.
(*NOREUSE*) Print Assumptions M2.g.
(*NOREUSE*) Print Assumptions M1.f.
(*NOREUSE*) Print Assumptions M2.f.
(*NOREUSE*) Print Assumptions M1.g.

Import M1.
(*NOREUSE*) Print Assumptions g.
(*NOREUSE*) Print Assumptions f.

Import M2.
(*NOREUSE*) Print Assumptions g.
(*NOREUSE*) Print Assumptions f.

Import M1.
(*NOREUSE*) Print Assumptions g.
(*NOREUSE*) Print Assumptions f.
