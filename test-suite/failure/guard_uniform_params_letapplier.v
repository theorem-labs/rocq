(* A closed proof of False that the 9.2 release accepts today, found while
   measuring this branch (binary-equivalence-taiga, dispatch://BET-214,
   2026-10-25). It uses no axiom and no typing flag: before this branch it
   compiles, Print Assumptions says "Closed under the global context", and
   coqchk -o reports no axiom and no unsafe fixpoint.

   It is the red-team agent's original file (test-suite/failure/
   guard_uniform_params.v, first definition) with one change: the function
   that receives the inner fixpoint unapplied is bound with [let] instead of
   being written as an inline lambda. That moves the head of the application
   from a Lambda to a Rel, and the uniform-parameter analysis folds over the
   arguments of a Rel-headed application by visiting each argument's children.
   A bare occurrence of the inner fixpoint is a Rel and has no children, so it
   was never seen, the prefix stayed uniform, and the subterm information of
   the first argument ever passed there was carried into the hidden call.

   Upstream dies on this one with
   Anomaly "Uncaught exception Failure("List.skipn")" rather than accepting
   it. This branch bounds the prefix instead: an unapplied occurrence allows
   no uniform prefix, so there is nothing to drop and nothing to assume, and
   an occurrence that still carries too few arguments refuses the definition
   rather than dropping what it can. *)

Inductive T : Set := C : T -> T | L : T.
Definition P (t : T) : Type := match t with L => unit | C _ => False end.
Definition R (u : T) (k : nat) : Type := match k with O => P u | S _ => False end.
Fail Fixpoint f (t : T) : P t :=
  match t as t0 return P t0 with
  | L => tt
  | C t' =>
      (fix g (u : T) (k : nat) {struct k} : R u k :=
         match k as k0 return R u k0 with
         | O => f u
         | S k' =>
             let app := fun h : forall (u : T) (k : nat), R u k => h (C t') k' in
             match k' as k0 return (R (C t') k0 -> False) with
             | O => fun x => x
             | S _ => fun x => x
             end (app g)
         end) t' (S O)
  end.
