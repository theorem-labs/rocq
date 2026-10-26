(* A terminating fixpoint whose own function occurs only in a cast TYPE of its
   binder prefix. Nothing evaluates a cast type, so the prefix walk erases it
   and accepts the definition, as stock Rocq 9.0.1 does. Found by the review of
   the substitution commit (dispatch://BET-214). *)
Definition compat_cast : nat -> nat.
Proof.
  fix f 1.
  refine (_ : (fun _ : nat -> nat => nat -> nat) f).
  intro n.
  destruct n as [|p].
  - exact O.
  - exact (f p).
Defined.
Check (eq_refl : compat_cast 3 = 0).
