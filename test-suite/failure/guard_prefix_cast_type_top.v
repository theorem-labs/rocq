(* Red on the release-7 rule: compiled with coqchk 0, Eval cbv overflows the stack. A cast type is now a position of the prefix walk. dispatch://BET-214 *)
(* Top-level fixpoint. The call's let is read only in a cast TYPE in the
   prefix; the walk follows a cast's term, never its type. *)
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
