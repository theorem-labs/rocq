(* Top-level fixpoint. The call's let is read only in a cast TYPE in the
   prefix. The release-7 cut 18da2c8ff497 calls the let live and never
   checks its value: it accepts the definition with "Closed under the global
   context" and `coqchk -o -norec` exit 0, and `Eval cbv` on it overflows
   the stack (Port90's bug-finder file f4b). The prefix walk now erases cast
   types, so x is dead and its value is checked. Ported from
   9.0/guard-cofix-prefix ebe9febceafe. dispatch://BET-214 *)
Definition top_castty : nat -> nat.
Proof.
  fix f 1.
  refine (let x := f (S O) in (_ : (fun _ : nat => nat -> nat) x)).
  intro n.
  destruct n as [|p].
  - exact O.
  - exact (f p).
Fail Defined.
Abort.
