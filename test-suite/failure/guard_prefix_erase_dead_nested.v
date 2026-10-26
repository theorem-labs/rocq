(* The nested form of guard_prefix_erase_dead_top.v: the inner fixpoints
   prefix hides the call behind two let annotations. Red on 2ebccafb3188 and on
   9e24663c6e07. dispatch://BET-214 *)
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
