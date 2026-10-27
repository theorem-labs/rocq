(* The raw-prefix rule takes head-reduction steps (delta, iota of a match or
   a projection on a constructor) to find the abstractions of a top-level
   fixpoint written behind a definition or a let-pattern
   (success/guard_prefix_let_pattern.v). Each step drops material, and a
   full recursive call in it is checked by nothing and still evaluated, so
   each body below must stay refused. Stock 9.2.0 and upstream master accept
   all eight with "Closed under the global context"; the walk without the
   steps refuses them as whole terms, and release-7 18da2c8ff497 accepts
   [top_pattern_dead], because its walk does not follow the let. *)

(* delta of a constant, then a beta step whose binder is dead *)
Definition drop (a : nat) (g : nat -> nat) : nat -> nat := g.
Definition top_drop_const : nat -> nat.
Proof.
  fix f 1.
  refine (drop (f (S O)) _).
  intro n. destruct n as [|p].
  - exact O.
  - exact (f p).
  Fail Defined.
Abort.

(* iota of a let-pattern that drops the field holding the call *)
Definition top_drop_field : nat -> nat.
Proof.
  fix f 1.
  refine (let (_, g) := (f (S O), fun n : nat => match n with O => O | S p => f p end) in g).
  Fail Defined.
Abort.

(* the Equations shape, with the call in the pair and a dead beta binder *)
Definition top_pattern_dead : nat -> nat.
Proof.
  pose (H := fun h : nat -> nat =>
    (fun n : nat => match n with O => O | S p => h p end, h (S O))).
  fix f 1.
  refine (let H := H f in let (s, p) := H in (fun (s0 : nat -> nat) (_ : nat) => s0) s p).
  Fail Defined.
Abort.

(* a dead beta argument while the scrutinee is reduced *)
Definition top_scrut_dead_beta : nat -> nat.
Proof.
  fix f 1.
  refine (match (fun _ : nat => (fun n : nat => match n with O => O | S p => f p end, tt)) (f (S O)) with
          | (g, _) => g end).
  Fail Defined.
Abort.

(* the branch a decided match does not select *)
Definition top_unselected : nat -> nat.
Proof.
  pose (sel := fun (h : nat -> nat) (b : bool) =>
    if b then (fun n : nat => match n with O => O | S p => h p end) else (fun _ : nat => h (S O))).
  fix f 1.
  refine (sel f true).
  Fail Defined.
Abort.

(* a parameter of the constructor (behind the constant [K], so that
   elaboration keeps the call in the term) *)
Definition K (n : nat) : Type := nat -> nat.
Definition top_ctor_param : nat -> nat.
Proof.
  fix f 1.
  refine (let (g, _) := @pair (K (f (S O))) unit
                          (fun n : nat => match n with O => O | S p => f p end) tt in g).
  Fail Defined.
Abort.

(* the field a primitive projection does not select *)
Set Primitive Projections.
Record R := mkR { r1 : nat; r2 : nat -> nat }.
Unset Primitive Projections.
Definition top_proj_field : nat -> nat.
Proof.
  fix f 1.
  refine ((mkR (f (S O)) (fun n : nat => match n with O => O | S p => f p end)).(r2)).
  Fail Defined.
Abort.

(* the return predicate of a decided match *)
Definition top_return_pred : nat -> nat.
Proof.
  fix f 1.
  refine (match tt return K (f (S O)) with
          | tt => fun n : nat => match n with O => O | S p => f p end end).
  Fail Defined.
Abort.
