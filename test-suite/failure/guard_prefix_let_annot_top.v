(* Red on the release-7 rule: compiled with coqchk 0, and Eval cbv overflows the
   stack (cbv computes x although only a type reads it). The prefix walk now
   erases let annotations, so x is dead and its value is checked.
   dispatch://BET-214 *)
(* Top-level fixpoint. The call's let is read only in the TYPE annotation
   of a later let, which raw_prefix_escapes never inspects. *)
Definition top_annot : nat -> nat.
Proof.
  fix f 1.
  pose (x := f (S O)).
  refine (let y : (fun _ : nat => nat) x := O in _).
  intro n.
  destruct n as [|p].
  - exact O.
  - exact (f p).
Fail Defined.
Abort.
