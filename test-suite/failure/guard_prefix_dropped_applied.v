(* The companion of success/guard_prefix_dropped_inert.v: material the
   binder-prefix reduction drops that mentions the block in a position where
   a reduction can still APPLY it. Each definition here is refused, on the
   guard checker's own line.

   Stock Rocq 9.2.0 accepts all of them; `Eval cbv` on the first, the fifth
   and the sixth there dies with "Error: Stack overflow", which is what an
   accepted body that is not strongly normalizing looks like. This fork
   refuses them deliberately, as it refuses the whole dropped-full-call
   family (test-suite/failure/guard_prefix_attack_let.v and its siblings).

   Each definition was also compiled on its own, with the `Fail` removed, to
   check that what fails is the guard and not the proof script: every one
   prints "Recursive definition of <f> is ill-formed.", with the subjects
   inner, inner, inner, inner, outer, f2, inner and f in the order below. *)

(* The dropped value hands a PARTIAL application of the block to a parameter
   that can apply it. *)
Definition applicator_type := (unit -> nat -> nat) -> unit.
Definition dropped_applicator : applicator_type -> unit -> nat -> nat.
Proof.
  fix inner 3.
  intro g.
  pose (dead := g (inner g)).
  intros x m.
  destruct m as [|k].
  - exact O.
  - exact (inner g x k).
  Fail Defined.
Abort.

(* The same, reached through a binder the prefix reads. *)
Definition dropped_applicator_alias : applicator_type -> unit -> nat -> nat.
Proof.
  fix inner 3.
  intro g.
  pose (h := inner g).
  pose (dead := g h).
  intros x m.
  destruct m as [|k].
  - exact O.
  - exact (inner g x k).
  Fail Defined.
Abort.

(* The same, behind a constant whose unfolding would erase the argument. *)
Definition keep (A B : Type) (a : A) (b : B) : B := b.
Definition dropped_applicator_constant
  : applicator_type -> unit -> nat -> nat.
Proof.
  fix inner 3.
  intro g.
  pose (dead := keep unit nat (g (inner g)) O).
  intros x m.
  destruct m as [|k].
  - exact O.
  - exact (inner g x k).
  Fail Defined.
Abort.

(* A dropped PARTIAL application whose argument is a full call on a
   non-decreasing argument. *)
Definition dropped_partial_bad_arg : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat -> nat) p p p).
    fix inner 3.
    pose (dead := inner (inner O O (S O))).
    intros a b m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a b k).
  Fail Defined.
Abort.

(* The ENCLOSING function handed to a parameter that applies it to a bigger
   number. *)
Definition dropped_enclosing_applicator : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : ((nat -> nat) -> nat) -> nat -> nat) (fun f => f (S (S p))) p).
    fix inner 2.
    intro h.
    pose (dead := h outer).
    intro m.
    destruct m as [|k].
    + exact O.
    + exact (inner h k).
  Fail Defined.
Abort.

(* A mutual block whose functions have different structural indices: [f1]
   applied to one argument is a FULL call, although the walk is in [f2]'s
   body, whose index is 1. *)
Definition dropped_mutual_index : nat -> nat.
Proof.
  fix f1 1 with (f2 (a m : nat) {struct m} : nat).
  - intro n. destruct n as [|p].
    + exact O.
    + exact (f2 (S p) p).
  - intro a.
    pose (dead := f1 (S a)).
    intro m. destruct m as [|k].
    + exact O.
    + exact (f2 a k).
  Fail Defined.
Abort.

(* Two costs of the rule, both refused although stock accepts them: the
   block sits inside the dropped term rather than at its head, and a dropped
   FULL call whose structural argument is built by eliminating False. *)
Definition dropped_inside_constructor : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := (inner, O)).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a k).
  Fail Defined.
Abort.

Definition dropped_dead_code_call : False -> nat -> nat.
Proof.
  fix f 2.
  intro e.
  pose (dead := f e (match e return nat with end)).
  intro n.
  destruct n as [|k].
  - exact O.
  - exact (f e k).
  Fail Defined.
Abort.

(* A match in the prefix whose scrutinee is a constructor with the block as an
   inductive PARAMETER and a let-in whose value is a FULL call of the block.
   The match parameter is dropped by iota, but the constructor's let-in value
   reads it and call-by-value computes that value, so a binding that records
   an unread parameter as "reaches nothing" would hide a full call (`Eval cbv`
   overflows the stack on it). *)
Inductive box (f : nat -> nat -> nat) : Type :=
  mk : forall (z : nat), let y := f z z in (nat -> nat -> nat) -> box f.
Arguments mk {f} _ _.
Definition dropped_param_letin : nat -> nat -> nat.
Proof.
  fix inner 2.
  refine (match @mk inner 0 (_ : nat -> nat -> nat) return nat -> nat -> nat with
          | @mk _ z h => h
          end).
  intros a m. destruct m as [|k].
  - exact O.
  - exact (inner a k).
  Fail Defined.
Abort.
