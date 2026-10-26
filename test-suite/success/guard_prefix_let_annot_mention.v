(* A terminating fixpoint whose own function occurs only in a let ANNOTATION
   of its binder prefix. Nothing evaluates an annotation, so the prefix walk
   erases it and accepts the definition, as stock Rocq 9.0.1 does. Found by
   the review of the substitution commit (dispatch://BET-214). *)
Definition compat_annot : nat -> nat.
Proof.
  fix f 1.
  refine (let y : (fun _ : nat -> nat => nat) f := O in _).
  intro n.
  destruct n as [|p].
  - exact O.
  - exact (f p).
Defined.
Check (eq_refl : compat_annot 3 = 0).
