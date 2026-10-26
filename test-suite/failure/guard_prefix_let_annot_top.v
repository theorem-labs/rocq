(* Top-level fixpoint. The call's let is read only in the TYPE annotation
   of a later let. The release-7 cut 18da2c8ff497 calls the let live and
   never checks its value: it accepts the definition with "Closed under the
   global context" and `coqchk -o -norec` exit 0, and `Eval cbv` on it
   overflows the stack, because cbv computes x although only a type reads it
   (Port90's bug-finder file f4). The prefix walk now erases let
   annotations, so x is dead and its value is checked. Ported from
   9.0/guard-cofix-prefix ebe9febceafe. dispatch://BET-214 *)
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
