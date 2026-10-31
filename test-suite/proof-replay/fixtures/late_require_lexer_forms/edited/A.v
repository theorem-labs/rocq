(* Each Require after the first proof names only a loaded library, so it
   loads nothing and is not a late command, but only when the source scan
   reads it in full. Each one is written in a form that the Require reader
   read with a lexer of its own before the late-command scan and the reader
   shared one cursor (code-quality finding MQ-2): a nested comment that holds
   a string with a comment end in it, a sentence over lines with a comment
   in it, an attribute then Export, and an import filter. A Require that the
   scan cannot read stays late, and every proof before it runs its tactics.
   So each proof must hit. *)
Require PR.Lib.
Lemma p1 : True.
Proof. exact I. Qed.
Require (* a (* "*)" b *) c *) PR.Lib.
Lemma p2 : True.
Proof. exact I. Qed.
From
  PR (* a comment
  over two lines *) Require
  Lib.
Lemma p3 : True.
Proof. exact I. Qed.
#[warnings="-deprecated"] Require Export PR.Lib.
Lemma p4 : True.
Proof. exact I. Qed.
Require Import PR.Lib(t).
Lemma p5 : True.
Proof. exact I. Qed.
