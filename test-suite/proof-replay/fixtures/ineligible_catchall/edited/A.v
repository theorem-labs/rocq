(* The `catchall` reason fires when one of the five instrumented handlers
   catches a CRITICAL exception (`lib/cErrors.ml:165-170`: Stack_overflow,
   Out_of_memory, Assert_failure, Match_failure, Anomaly, Control.Timeout,
   Sys.Break).  This fixture reaches the handler at `tactics/equality.ml:466`.

   `rewrite H` on a user equality calls `lookup_eq_eliminator_opt`
   (`equality.ml:523`).  For an equality that is neither `eq` nor `identity`
   there is no registered scheme, so it goes on to `lookup_eq_eliminator_tc`,
   which runs `Class_tactics.resolve_one_typeclass` over the hint database
   `rewrite_instances` (`equality.ml:209,432-440`).  A `Hint Extern` in that
   database therefore runs INSIDE the handler's `try`.

   The hint below reduces a one-million-deep term.  Reading the result back
   recurses once per constructor, so it overflows the 8 MB stack the fixture
   pins, which is the stack a grade runs under.  The handler catches it, marks
   the open proof `catchall`, and returns None; `rewrite` then takes its
   fallback (`gen_elim`, `equality.ml:526`), which builds the rewriting scheme
   for `myeq`, so the proof still closes and the compile still succeeds.

   The control that this is the handler and not some other part of the
   compile: the same reduction written INSIDE the proof instead of inside the
   hint ends the compile with "Stack overflow" and writes no record at all
   (measured 2026-10-25 on speed-r1, `~/r1-p3fix3/sweep2/cat_control_inproof`).
   `cbv` and `lazy` in place of `vm_compute` mark the proof just the same. *)
Inductive myeq (A : Type) (x : A) : A -> Prop := myeq_refl : myeq A x x.

Fixpoint tower (n : nat) : nat := match n with O => O | S m => S (tower m) end.

Definition pad := 0.

Lemma control : True.
Proof. exact I. Qed.

#[local] Hint Extern 0 => (let _ := eval vm_compute in (tower 4000000) in idtac) : rewrite_instances.

Lemma catchall_proof : forall x y : nat, myeq nat x y -> x = y.
Proof. intros x y H. rewrite H. reflexivity. Qed.
