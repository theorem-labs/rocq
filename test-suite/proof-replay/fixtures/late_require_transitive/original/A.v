(* PR.Top requires PR.Dep, so the first line loads PR.Dep too. The later
   Require of PR.Dep loads nothing, and the proof before it replays. *)
Require PR.Top.
Lemma p : True.
Proof. exact I. Qed.
Require Import PR.Dep.
Lemma q : True.
Proof. exact I. Qed.
