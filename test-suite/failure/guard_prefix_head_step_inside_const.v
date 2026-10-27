(* The bodies of guard_prefix_head_step_drops.v with the step that drops
   the call moved INSIDE the constant or section variable the walk
   unfolds, and one whose branch body reads an outer let while the walk
   binds the match's parameters in front of the constructor's
   declarations. Each must be refused, as the plain shapes are: the
   reduction drops a full call [f (S O)] in every one of them. Stock 9.2.0
   accepts them all. The same bodies with [O] in place of the call are in
   success/guard_prefix_head_step_inside_const.v. *)

(* a dead beta redex inside the constant *)
Definition drop2 (a : nat) (g : nat -> nat) : nat -> nat :=
  (fun (_ : nat) (h : nat -> nat) => h) a g.
Definition top_const_dead_beta : nat -> nat.
Proof.
  fix f 1.
  refine (drop2 (f (S O)) _).
  intro n. destruct n as [|p].
  - exact O.
  - exact (f p).
  Fail Defined.
Abort.

(* a dead let inside the constant *)
Definition dropl (a : nat) (g : nat -> nat) : nat -> nat :=
  let _ := a in g.
Definition top_const_dead_let : nat -> nat.
Proof.
  fix f 1.
  refine (dropl (f (S O)) (fun n : nat => match n with O => O | S p => f p end)).
  Fail Defined.
Abort.

(* a constructor parameter dropped by an iota inside the constant *)
Definition K (n : nat) : Type := nat -> nat.
Definition dropp (a : nat) (g : nat -> nat) : nat -> nat :=
  let (h, _) := @pair (K a) unit g tt in h.
Definition top_const_ctor_param : nat -> nat.
Proof.
  fix f 1.
  refine (dropp (f (S O)) (fun n : nat => match n with O => O | S p => f p end)).
  Fail Defined.
Abort.

(* the same dead beta redex inside a section variable's value *)
Section S.
  Let dropv (a : nat) (g : nat -> nat) : nat -> nat :=
    (fun (_ : nat) (h : nat -> nat) => h) a g.
  Definition top_sectionvar_dead_beta : nat -> nat.
  Proof.
    fix f 1.
    refine (dropv (f (S O)) (fun n : nat => match n with O => O | S p => f p end)).
    Fail Defined.
  Abort.
End S.

(* the branch body is an outer let whose own head reduction drops the
   call; the walk binds the inductive types and the match's parameters in
   front of the constructor's declarations, and the branch body must still
   read the let *)
Definition drop1 (a : nat) (g : nat -> nat) : nat -> nat := g.
Inductive TT : Type := mk (a : nat) (b := a) (g : nat -> nat).
Definition top_branch_shift : nat -> nat.
Proof.
  fix f 1.
  refine (let k := drop1 (f (S O)) (fun n : nat => match n with O => O | S p => f p end) in
          match mk O (fun _ : nat => O) with
          | mk a g => k
          end).
  Fail Defined.
Abort.

(* a PARAMETER of an inductive that has a let-in parameter, dropped by the
   iota, holding the call *)
Definition KT (n : nat) : Type := nat.
Inductive TR (A : Type) (B := A) (C := A) : Type :=
  mkr : forall (x : nat -> nat), let y := A in C -> (nat -> nat) -> TR A.
Definition top_letparam_dropped : nat -> nat.
Proof.
  fix f 1.
  refine (let r := (fun n : nat => match n with O => O | S p => f p end) in
          match mkr (KT (r (S O))) (fun k : nat => k) O r return nat -> nat with
          | mkr _ _ _ x y b h => h
          end).
  Fail Defined.
Abort.
