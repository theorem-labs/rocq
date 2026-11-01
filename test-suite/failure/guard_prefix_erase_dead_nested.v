(* The nested form of guard_prefix_erase_dead_top.v: the inner fixpoint's
   prefix hides the call behind a let annotation. The release-7 cut
   18da2c8ff497 accepts the definition (this file fails there with "The
   command has not failed!"). Ported from 9.0/guard-cofix-prefix
   ebe9febceafe. dispatch://BET-214 *)
Definition erase_dead_nested : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (let x := outer (S (S p)) in
            let y : (fun _ : nat => nat) x := O in
            (fun a m : nat => _)).
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Fail Defined.
Abort.
