(* A Require after the first proof that names only loaded libraries loads
   nothing: no object's load function runs and no plugin loads. So it is
   not a late command, and the proof before it replays. The first line
   loads PR.Lib; the prelude loads Init.Datatypes. *)
Require PR.Lib.
Lemma p : True.
Proof. exact I. Qed.
Require Import PR.Lib.
From Corelib Require Import Init.Datatypes.
Lemma q : True.
Proof. exact I. Qed.
