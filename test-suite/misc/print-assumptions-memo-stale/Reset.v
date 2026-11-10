(* A constant redefined under its own name after Reset. Reset rolls the
   environment back, and the commands after it build other constants under
   the names the rolled-back ones had, so nothing recorded before it may be
   replayed after it.

   The (*NOREUSE*) marks are where the control arm of
   print-assumptions-memo-stale.sh puts a definition of its own, which
   changes the environment and so leaves every query a walk without reuse.
   The warning Reset prints in batch mode is located at the command before
   it, whose column the control arm moves, so it is turned off here and both
   arms print nothing on standard error. *)

Set Warnings "-undo-batch-mode".

Axiom ax1 : nat.
Axiom ax2 : nat.

Definition d : nat.
Proof. exact ax1. Qed.
Definition e : nat := d.
(*NOREUSE*) Print Assumptions e.
(*NOREUSE*) Print Assumptions d.

Reset d.

Definition d : nat.
Proof. exact ax2. Qed.
Definition e : nat := d.
(*NOREUSE*) Print Assumptions e.
(*NOREUSE*) Print Assumptions d.
