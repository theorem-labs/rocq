(* An occurrence of a function of the block that the binder-prefix reduction
   DROPS, and that carries at most its structural index of arguments, is
   discarded unapplied by every reduction: it can make no recursive call. The
   prefix walk lets it through instead of refusing the definition.

   Stock Rocq 9.2.0 accepts every definition here, and so does this fork
   since the commit that adds this file. The release before it refused all
   of them with "Not enough abstractions in the definition" (the first five
   are a bare occurrence, a partial application, a mutual block, a dead
   branch and an unselected branch).

   The companion failure file guard_prefix_dropped_applied.v holds the
   shapes that are still refused: an occurrence that something can apply. *)

(* D1: a bare occurrence in a local definition of the prefix. *)
Definition dropped_bare : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := inner).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a k).
Defined.
Example dropped_bare_computes : dropped_bare 5 = 0. Proof. reflexivity. Qed.

(* D3: a PARTIAL application, one argument where the structural index is 3. *)
Definition dropped_partial : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat -> nat) p p p).
    fix inner 3.
    pose (part := inner O).
    intros a b m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a b k).
Defined.
Example dropped_partial_computes : dropped_partial 5 = 0.
Proof. reflexivity. Qed.

(* D6: a mutual inner block, the occurrence in the prefix of the SECOND body
   and naming the first function. *)
Definition dropped_mutual : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner1 2 with (inner2 (a m : nat) {struct m} : nat).
    + intros a m.
      destruct m as [|k].
      * exact (outer p).
      * exact (inner2 a k).
    + pose (dead := inner1).
      intros a m.
      destruct m as [|k].
      * exact O.
      * exact (inner2 a k).
Defined.
Example dropped_mutual_computes : dropped_mutual 5 = 0. Proof. reflexivity. Qed.

(* D14: the same, in a branch of a match on [O] that is never taken. *)
Definition dropped_dead_branch : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine (match O with
            | O => outer p
            | S _ => (_ : nat -> nat -> nat) p p
            end).
    fix inner 2.
    pose (dead := inner).
    intros a m.
    destruct m as [|k].
    + exact O.
    + exact (inner a k).
Defined.
Example dropped_dead_branch_computes : dropped_dead_branch 5 = 0.
Proof. reflexivity. Qed.

(* D15: the occurrence is the branch a match on [O] does not select. *)
Definition dropped_unselected : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (match O return nat -> nat -> nat with
            | O => _
            | S _ => inner
            end).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a k).
Defined.
Example dropped_unselected_computes : dropped_unselected 5 = 0.
Proof. reflexivity. Qed.

(* The unselected branch is an abstraction over a partial application: the
   walk goes under the abstraction before it reads the head. *)
Definition dropped_under_lambda : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (match O return nat -> nat -> nat with
            | O => _
            | S _ => fun a => inner a
            end).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a k).
Defined.
Example dropped_under_lambda_computes : dropped_under_lambda 5 = 0.
Proof. reflexivity. Qed.

(* The dropped value reaches the block through a binder the prefix reads:
   [h] is read only by the dropped [h O]. *)
Definition dropped_through_alias : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (h := inner).
    pose (dead := h O).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a k).
Defined.
Example dropped_through_alias_computes : dropped_through_alias 5 = 0.
Proof. reflexivity. Qed.

(* The dropped occurrence is of the ENCLOSING function, which the nested
   walk of check_one_fix holds to the same rule. *)
Definition dropped_enclosing : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := outer).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a k).
Defined.
Example dropped_enclosing_computes : dropped_enclosing 5 = 0.
Proof. reflexivity. Qed.
