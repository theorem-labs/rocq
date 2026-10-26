(* Top-level fixpoint. The call's let is read only in the branch of a
   decided match that the reduction does not select. After the let is
   substituted, the call sits in that branch, inside the match the walk
   checks as a whole term. The release-7 cut 18da2c8ff497, whose walk does
   not substitute the let, sees only "Rel x" there and accepts the
   definition with "Closed under the global context" and `coqchk -o -norec`
   exit 0, and `Eval cbv` on it overflows the stack (Port90's bug-finder
   file f7). Ported from 9.0/guard-cofix-prefix 9e24663c6e07.
   dispatch://BET-214 *)
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
