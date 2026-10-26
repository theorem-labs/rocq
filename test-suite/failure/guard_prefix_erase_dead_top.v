(* The calls let is read only in a let ANNOTATION, and that let is read only
   in a second annotation. Erasing the chains types makes all three lets dead,
   so the value "f (S O)" is reported. Red on 2ebccafb3188 (the release-7 rule)
   and on 9e24663c6e07: both accept it with coqchk 0, and Eval cbv then
   computes f (S O) for ever. dispatch://BET-214 *)
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
