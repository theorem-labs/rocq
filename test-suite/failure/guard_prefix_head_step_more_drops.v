(* More material that a head-reduction step of the raw-prefix rule drops:
   each body puts the full call [f (S O)] there (in the last one, a call of
   the enclosing [outer] on a bigger argument), and must be refused, as in
   guard_prefix_head_step_drops.v. The same bodies with [O] in place of the
   call are accepted (success/guard_prefix_head_step.v). Stock 9.2.0
   accepts each of them. *)

(* the argument of a constructor whose binder only a let-in of the
   constructor reads, and that let-in is not read *)
Inductive T : Type := mk (a : nat) (b := a) (g : nat -> nat).
Definition top_ctor_letin_dead : nat -> nat.
Proof.
  fix f 1.
  refine (match mk (f (S O)) (fun n : nat => match n with O => O | S p => f p end) with
          | mk a g => g end).
  Fail Defined.
Abort.

(* an argument of a match that its branch does not read *)
Definition top_match_applied_dead : nat -> nat.
Proof.
  fix f 1.
  refine ((match tt return nat -> nat -> nat with
           | tt => fun (x : nat) => fun n : nat => match n with O => O | S p => f p end end)
            (f (S O))).
  Fail Defined.
Abort.

(* a primitive projection of a let-bound record whose other field is the
   call (release-7 18da2c8ff497 accepts this one) *)
Set Primitive Projections.
Record R := mkR { r1 : nat; r2 : nat -> nat }.
Unset Primitive Projections.
Definition top_proj_via_let : nat -> nat.
Proof.
  fix f 1.
  refine (let r := mkR (f (S O)) (fun n : nat => match n with O => O | S p => f p end) in r.(r2)).
  Fail Defined.
Abort.

(* a let-pattern on a let-bound pair whose first field is the call
   (release-7 accepts this one) *)
Definition top_letpat_used_let_dead : nat -> nat.
Proof.
  fix f 1.
  refine (let p := (f (S O), fun n : nat => match n with O => O | S p => f p end) in
          let (a, h) := p in h).
  Fail Defined.
Abort.

(* the argument of the selected constructor, not read by the branch *)
Definition top_select_S_dead : nat -> nat.
Proof.
  fix f 1.
  refine (match S (f (S O)) with
          | O => (fun _ : nat => O)
          | S q => (fun n : nat => match n with O => O | S p => f p end) end).
  Fail Defined.
Abort.

(* the first branch, when the second is selected *)
Definition top_unselected_first : nat -> nat.
Proof.
  fix f 1.
  refine (if false then (fun _ : nat => f (S O))
          else (fun n : nat => match n with O => O | S p => f p end)).
  Fail Defined.
Abort.

(* a parameter of the second constructor of [sum] *)
Definition K (n : nat) : Type := nat.
Definition top_inr_param : nat -> nat.
Proof.
  fix f 1.
  refine (match @inr (K (f (S O))) unit tt with
          | inl _ => (fun _ : nat => O)
          | inr _ => (fun n : nat => match n with O => O | S p => f p end) end).
  Fail Defined.
Abort.

(* a dead let at the head of an application *)
Definition top_letin_app_dead : nat -> nat.
Proof.
  fix f 1.
  refine ((let x := f (S O) in fun g : nat -> nat => g)
            (fun n : nat => match n with O => O | S p => f p end)).
  Fail Defined.
Abort.

(* the argument of a constructor whose type is a let-in parameter *)
Inductive W (A : Type) (B := A) : Type := mkW (x : B) (h : nat -> nat).
Definition top_letin_param_dead : nat -> nat.
Proof.
  fix f 1.
  refine (match mkW nat (f (S O)) (fun n : nat => match n with O => O | S p => f p end) with
          | mkW _ x h => h end).
  Fail Defined.
Abort.

(* the field before a let field, not selected by the projection *)
Set Primitive Projections.
Record R3 := mkR3 { a3 : nat; b3 := a3; c3 : nat -> nat }.
Unset Primitive Projections.
Definition top_prim_letfield_dead : nat -> nat.
Proof.
  fix f 1.
  refine ((mkR3 (f (S O)) (fun n : nat => match n with O => O | S p => f p end)).(c3)).
  Fail Defined.
Abort.

(* a nested fixpoint whose head drops a call of the ENCLOSING function on a
   bigger argument; the enclosing block's check refuses it *)
Definition dropn (a : nat) (g : nat -> nat) : nat -> nat := g.
Definition outer_drop : nat -> nat.
Proof.
  fix outer 1. intro n. destruct n as [|m].
  - exact O.
  - refine ((_ : nat -> nat) m). fix inner 1.
    refine (dropn (outer (S m)) _).
    intro k. destruct k as [|j].
    + exact (outer m).
    + exact (inner j).
  Fail Defined.
Abort.
