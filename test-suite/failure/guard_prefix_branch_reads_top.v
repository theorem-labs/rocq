(* Red on the release-7 rule: compiled with coqchk 0, Eval cbv overflows the stack. After the let is substituted, the call sits in the branch the decided match does not select, inside the match the walk checks as a whole. dispatch://BET-214 *)
(* Top-level fixpoint. The call's let is read only in the branch of a
   decided match that the reduction does not select; the walk checks the
   match as a whole term, where the call is only "Rel x". *)
Definition top_branch : nat -> nat.
Proof.
  fix f 1.
  refine (let x := f (S O) in
          match O return nat -> nat with
          | O => fun n : nat => O
          | S _ => fun n : nat => x
          end).
Fail Defined.
Abort.
