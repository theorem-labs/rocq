(* A non-terminating fixpoint that the 9.2 base, Rocq 9.2.0 and Rocq 9.3+rc1
   all ACCEPT, with Print Assumptions reporting "Closed under the global
   context" and coqchk reporting no axiom and no unsafe fixpoint. This branch
   refuses it. Found by the review of this branch
   (binary-equivalence-taiga, dispatch://BET-214, 2026-10-25).

   The inner fixpoint's recursive call [f (S a) k] increases its first
   argument, so nothing decreases along the chain [outer a] re-entered from
   the inner loop. The analysis was kept from seeing the recursive call at
   all: the body's head is a local definition, and the lookup that resolves it
   happened in an environment that does not hold the inner fixpoint's own
   declarations, so the indices were off by the size of the block and a decoy
   was analysed in its place. With the arguments of recursive calls analysed
   and the prefix bounded by every occurrence, the real body is measured and
   the definition is refused. *)

Definition outerX7 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - pose (decoy := fun (x a m : nat) => O).
    pose (hdef := fun (f : nat -> nat -> nat) (a m : nat) =>
                    match m with
                    | O => outer a
                    | S k => f (S a) k
                    end).
    refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    exact (hdef (fun a m => inner a m)).
  Fail Defined.
Abort.
