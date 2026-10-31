(* The import filter t(.. ) holds ".." then a blank. Rocq's lexer reads
   ".." as one token, which does not end a sentence, so the source scan reads
   this Require in full. It names only a loaded library, so it is not a late
   command, and the proof before it replays. Before the late-command scan
   and the Require reader shared one cursor, the reader took that ".." for
   the end of the sentence: the Require stayed late, and p ran its tactics. *)
Require PR.Lib.
Lemma p : True.
Proof. exact I. Qed.
Require Import PR.Lib(t(.. )).
Lemma q : True.
Proof. exact I. Qed.
