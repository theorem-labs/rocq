(* Queries across a module close and a section close. A module sealed by a
   signature answers with the axioms of its body while it is open, and with
   itself once it is closed; a section discharges its constants under the
   names they had inside it, over the section's variables. Both change what a
   query must answer, under names that were queried before.

   The (*NOREUSE*) marks are where the control arm of
   print-assumptions-memo-stale.sh puts a definition of its own, which
   changes the environment and so leaves every query a walk without reuse. *)

Axiom ax1 : nat.
Axiom ax2 : nat.

Module Type T.
  Parameter p : nat.
End T.

Module M : T.
  Definition p : nat := ax1.
  Definition q : nat := p.
  (*NOREUSE*) Print Assumptions p.
  (*NOREUSE*) Print Assumptions q.
  (*NOREUSE*) Print Assumptions p.
End M.

(*NOREUSE*) Print Assumptions M.p.
(*NOREUSE*) Print Assumptions M.p.

(* The same query inside another module, which the entries recorded outside
   it must not answer: a sealed constant is looked up through its module's
   implementation only while that implementation is visible, and opening a
   module changes that without changing the environment. *)
Module Inside.
  (*NOREUSE*) Print Assumptions M.p.
  (*NOREUSE*) Print Assumptions M.p.
End Inside.

(*NOREUSE*) Print Assumptions M.p.

Module N.
  Definition u : nat := ax2.
  (*NOREUSE*) Print Assumptions u.
  (*NOREUSE*) Print Assumptions u.
End N.

(*NOREUSE*) Print Assumptions N.u.
(*NOREUSE*) Print Assumptions N.u.

Section S.
  Variable v : nat.
  Let l : nat := ax1.
  Definition s : nat := v + l.
  Definition t : nat := s + ax2.
  (*NOREUSE*) Print Assumptions s.
  (*NOREUSE*) Print Assumptions t.
  (*NOREUSE*) Print Assumptions s.
End S.

(*NOREUSE*) Print Assumptions s.
(*NOREUSE*) Print Assumptions t.
(*NOREUSE*) Print Assumptions s.
