(* A module type with parameters, a functor over it, and the functor applied
   twice to declared parameters, with queries on constants of both
   applications in one session: the shape of a generated file that asks for
   the assumptions of two instances of one development. A third application
   repeats the first argument, so its constants hold the same terms under
   other canonical names.

   The (*NOREUSE*) marks are where the control arm of
   print-assumptions-memo-stale.sh puts a definition of its own, which
   changes the environment and so leaves every query a walk without reuse. *)

Axiom ax1 : nat.

Module Type T.
  Parameter p : nat.
  Parameter q : nat.
End T.

Module F (X : T).
  Definition h : nat := X.p + ax1.
  Definition h2 : nat := h + X.q.
End F.

Declare Module P1 : T.
Declare Module P2 : T.

Module A1 := F P1.
Module A2 := F P2.
Module A3 := F P1.

(*NOREUSE*) Print Assumptions A1.h2.
(*NOREUSE*) Print Assumptions A2.h2.
(*NOREUSE*) Print Assumptions A1.h2.
(*NOREUSE*) Print Assumptions A3.h2.
(*NOREUSE*) Print Assumptions A1.h.
(*NOREUSE*) Print Assumptions A2.h.
(*NOREUSE*) Print Assumptions A3.h.
(*NOREUSE*) Print Assumptions A1.h2.
