(* [Module.module_contents] in a tactic names Ltac2's module [Module]: one
   qualified identifier to Rocq's lexer, never a command. The source scan
   took the word [Module] there for a late command, so every proof that opens
   before it ran its tactics. All three proofs must replay. *)
From Ltac2 Require Import Ltac2.

Lemma first : True.
Proof. exact I. Qed.

Lemma second : True.
Proof. let _ := Module.module_contents (Module.current_module ()) in exact I. Qed.

Lemma third : True.
Proof. exact I. Qed.
