(* -*- coqchk-prog-args: ("-bytecode-compiler" "yes") -*- *)

(* VM conversion and the component index of a mutual fixpoint.

   [Vm.apply_whd] and [Vm.apply_stack] enter a fixpoint's own bytecode to
   expand a stuck value on the fly. They used to enter it with [fix_env f],
   which is already the block's LAST component, instead of the component [f]
   stands for. [GRABREC] records its [rocq_env] as the fixpoint of the
   accumulator it builds when the recursive argument is stuck, so every
   expansion reported the last component, and [Vconv.check_fix] then compared
   the wrong index: a component was not convertible with its own
   eta-expansion, and the last component was convertible with any other
   component of the same block. Both verdicts are wrong, and the second one
   is unsound.

   The accepting lemmas are checked twice: by [coqc], and again by
   [coqchk -bytecode-compiler yes] over the compiled file. The [Fail]
   commands are compile-time checks only — a refused cast leaves nothing in
   the [.vo] for the checker to re-examine — so they pin the refusing side
   at elaboration, where the same [Vconv] comparison runs.

   One component block is unaffected (its last component is itself), which is
   why only mutual fixpoints show this. *)

(* ------------------------------------------------------------------ *)
(* Partial application: the recursive argument is not the first one.   *)

Fixpoint ev (c n : nat) : nat :=
  match n with 0 => c | S m => od c m end
with od (c n : nat) : nat :=
  match n with 0 => S c | S m => ev c m end.

Lemma partial_eta : forall c, (fun n => ev c n) = ev c.
Proof.
  intro c.
  exact ((eq_refl : (fun n => ev c n) = (fun n => ev c n))
           <: ((fun n => ev c n) = ev c)).
Qed.

Lemma partial_eta_last : forall c, (fun n => od c n) = od c.
Proof.
  intro c.
  exact ((eq_refl : (fun n => od c n) = (fun n => od c n))
           <: ((fun n => od c n) = od c)).
Qed.

(* [ev c] and [od c] are different functions ([ev c 0 = c], [od c 0 = S c]),
   so the VM must refuse them. *)
Lemma partial_distinct : True.
Proof.
  Fail refine (let _ := ((eq_refl : (fun n => od 0 n) = (fun n => od 0 n))
                           <: ((fun n => od 0 n) = ev 0)) in I).
  exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* Three components: every one of them is its own eta-expansion.       *)

Fixpoint p (n : nat) : nat := match n with 0 => 0 | S m => q m end
with     q (n : nat) : nat := match n with 0 => 1 | S m => r m end
with     r (n : nat) : nat := match n with 0 => 2 | S m => p m end.

Lemma three_first  : (fun n => p n) = p.
Proof. exact ((eq_refl : (fun n => p n) = (fun n => p n)) <: ((fun n => p n) = p)). Qed.
Lemma three_middle : (fun n => q n) = q.
Proof. exact ((eq_refl : (fun n => q n) = (fun n => q n)) <: ((fun n => q n) = q)). Qed.
Lemma three_last   : (fun n => r n) = r.
Proof. exact ((eq_refl : (fun n => r n) = (fun n => r n)) <: ((fun n => r n) = r)). Qed.

(* and no two of them are convertible *)
Lemma three_distinct : True.
Proof.
  Fail refine (let _ := ((eq_refl : (fun n => r n) = (fun n => r n))
                           <: ((fun n => r n) = p)) in I).
  Fail refine (let _ := ((eq_refl : (fun n => r n) = (fun n => r n))
                           <: ((fun n => r n) = q)) in I).
  Fail refine (let _ := ((eq_refl : (fun n => q n) = (fun n => q n))
                           <: ((fun n => q n) = p)) in I).
  exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* The same through [apply_stack]: a stuck application of a mutual     *)
(* fixpoint that still returns a function.                            *)

Fixpoint fa (n : nat) : nat -> nat :=
  match n with 0 => fun x => x | S m => fb m end
with fb (n : nat) : nat -> nat :=
  match n with 0 => fun x => S x | S m => fa m end.

Lemma stack_eta : forall n, (fun x => fa n x) = fa n.
Proof.
  intro n.
  exact ((eq_refl : (fun x => fa n x) = (fun x => fa n x))
           <: ((fun x => fa n x) = fa n)).
Qed.

(* The recursive argument stays a variable, so the fixpoint is still stuck
   and the comparison really goes through the accumulator path. The binder
   sits INSIDE the [let], so the cast is pretyped with an empty tycon: with
   the binder outside, [refine] would reject the term against the goal
   [True] before ever elaborating the cast, and the [Fail] would pass
   whatever the VM decided. *)
Lemma stack_distinct : True.
Proof.
  Fail refine (let _ := (fun n : nat =>
                 ((eq_refl : (fun x => fb n x) = (fun x => fb n x))
                    <: ((fun x => fb n x) = fa n))) in I).
  exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* [apply_stack] again, with arguments AFTER the recursive one, so the  *)
(* stuck value carries a [Zapp] frame on top of its [Zfix] frame.       *)

Fixpoint ga (n x : nat) : nat -> nat :=
  match n with 0 => fun y => x + y | S m => gb m x end
with gb (n x : nat) : nat -> nat :=
  match n with 0 => fun y => x * y | S m => ga m x end.

Lemma stack_app_eta : forall n x, (fun y => ga n x y) = ga n x.
Proof.
  intros n x.
  exact ((eq_refl : (fun y => ga n x y) = (fun y => ga n x y))
           <: ((fun y => ga n x y) = ga n x)).
Qed.

Lemma stack_app_eta_last : forall n x, (fun y => gb n x y) = gb n x.
Proof.
  intros n x.
  exact ((eq_refl : (fun y => gb n x y) = (fun y => gb n x y))
           <: ((fun y => gb n x y) = gb n x)).
Qed.

Lemma stack_app_distinct : True.
Proof.
  Fail refine (let _ := (fun n x : nat =>
                 ((eq_refl : (fun y => gb n x y) = (fun y => gb n x y))
                    <: ((fun y => gb n x y) = ga n x))) in I).
  exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* GRABREC's PARTIAL-APPLICATION branch: eta-expanding before the       *)
(* recursive argument is supplied, so the fixpoint is entered with      *)
(* fewer arguments than its recursive position.                        *)

Lemma partial_before_rec : (fun c => ev c) = ev.
Proof.
  exact ((eq_refl : (fun c => ev c) = (fun c => ev c))
           <: ((fun c => ev c) = ev)).
Qed.

Lemma partial_before_rec_last : (fun c => od c) = od.
Proof.
  exact ((eq_refl : (fun c => od c) = (fun c => od c))
           <: ((fun c => od c) = od)).
Qed.

Lemma partial_before_rec_distinct : True.
Proof.
  Fail refine (let _ := ((eq_refl : (fun c => od c) = (fun c => od c))
                           <: ((fun c => od c) = ev)) in I).
  exact I.
Qed.
