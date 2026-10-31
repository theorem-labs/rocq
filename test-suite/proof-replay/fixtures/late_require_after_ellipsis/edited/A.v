(* "idtac..." ends its tactic sentence as "idtac." does: Rocq's lexer reads
   "..." then a blank as a sentence end. So From is the command word of the
   next sentence, and the source scan reads that Require in full. It names
   only a loaded library, so it is not a late command, and the proof before
   it replays. Before the late-command scan and the Require reader shared one
   cursor, the scan read no sentence end after "...": it could not read the
   Require, which stayed late, and p ran its tactics. The Require is a
   command inside q, so q is ineligible in any case. *)
Require PR.Lib.
Lemma p : True.
Proof. exact I. Qed.
Lemma q : True.
Proof with idtac. idtac... From PR Require Lib. exact I. Qed.
Lemma r : True.
Proof. exact I. Qed.
