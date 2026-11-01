(* The call's let is read only in a let ANNOTATION, and that let is read
   only in a second annotation. Erasing the chain's types makes all three
   lets dead, so the value "f (S O)" is reported. The release-7 cut
   18da2c8ff497 accepts the definition (this file fails there with "The
   command has not failed!"). Ported from 9.0/guard-cofix-prefix
   ebe9febceafe. dispatch://BET-214 *)
Definition erase_dead_top : nat -> nat.
Proof.
  fix f 1.
  pose (x := f (S O)).
  refine (let y : (fun _ : nat => nat) x := O in _).
  refine (let z : (fun _ : nat => nat) y := O in _).
  intro n.
  destruct n as [|p].
  - exact O.
  - exact (f p).
Fail Defined.
Abort.
