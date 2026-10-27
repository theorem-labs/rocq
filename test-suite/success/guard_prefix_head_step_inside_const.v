(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* The bodies of failure/guard_prefix_head_step_inside_const.v with [O] in
   place of the dropped call, plus the valid shapes of a constructor with
   let-ins: a branch body that reads an outer let, a declared let-in value
   that reads a parameter and one that reads the inductive type, and
   let-in parameters. Stock 9.2.0 accepts all of them; release-8
   a3a27a829aa2 refuses all of them ("Not enough abstractions in the
   definition"). Native compilation is off (rocq-prover/rocq#16599). *)

Definition drop2 (a : nat) (g : nat -> nat) : nat -> nat :=
  (fun (_ : nat) (h : nat -> nat) => h) a g.
Definition top_const_dead_beta : nat -> nat.
Proof.
  fix f 1.
  refine (drop2 O _).
  intro n. destruct n as [|p].
  - exact O.
  - exact (f p).
Defined.

Definition dropl (a : nat) (g : nat -> nat) : nat -> nat := let _ := a in g.
Definition top_const_dead_let : nat -> nat.
Proof.
  fix f 1.
  refine (dropl O (fun n : nat => match n with O => O | S p => f p end)).
Defined.

Definition K (n : nat) : Type := nat -> nat.
Definition dropp (a : nat) (g : nat -> nat) : nat -> nat :=
  let (h, _) := @pair (K a) unit g tt in h.
Definition top_const_ctor_param : nat -> nat.
Proof.
  fix f 1.
  refine (dropp O (fun n : nat => match n with O => O | S p => f p end)).
Defined.

Section S.
  Let dropv (a : nat) (g : nat -> nat) : nat -> nat :=
    (fun (_ : nat) (h : nat -> nat) => h) a g.
  Definition top_sectionvar_dead_beta : nat -> nat.
  Proof.
    fix f 1.
    refine (dropv O (fun n : nat => match n with O => O | S p => f p end)).
  Defined.
End S.

(* the branch body reads an outer let, while the walk binds the inductive
   types and the match's parameters in front of the constructor's
   declarations *)
Inductive TT : Type := mk (a : nat) (b := a) (g : nat -> nat).
Definition top_branch_ref : nat -> nat.
Proof.
  fix f 1.
  refine (let h := fun (u : nat -> nat) => u in
          match mk O (fun n : nat => match n with O => O | S p => f p end) with
          | mk a g => h g
          end).
Defined.

(* a declared let-in value that reads the constructor's parameter, and one
   that reads the inductive type *)
Definition idT (T : Type) (x : T) : T := x.
Inductive TQ (A : Type) : Type :=
  mkq (x : A) (y := idT Type A) (h : nat -> nat).
Definition top_ctorlet_reads_param : nat -> nat.
Proof.
  fix f 1.
  refine (match mkq nat O (fun n : nat => match n with O => O | S p => f p end)
                return nat -> nat with
          | mkq _ x y h => h
          end).
Defined.

(* two let-in parameters, so mind_params_ctxt is two declarations longer
   than ci_npar, with a declared let-in value reading a parameter *)
Inductive TR (A : Type) (B := A) (C := A) : Type :=
  mkr : forall (x : nat -> nat), let y := A in C -> (nat -> nat) -> TR A.
Definition top_letparam : nat -> nat.
Proof.
  fix f 1.
  refine (let r := (fun n : nat => match n with O => O | S p => f p end) in
          match mkr nat (fun k : nat => k) O r return nat -> nat with
          | mkr _ _ _ x y b h => h
          end).
Defined.

Example computes :
  (top_const_dead_beta 3, top_const_dead_let 3, top_const_ctor_param 3,
   top_sectionvar_dead_beta 3, top_branch_ref 3, top_ctorlet_reads_param 3,
   top_letparam 3) = (0, 0, 0, 0, 0, 0, 0) := eq_refl.
