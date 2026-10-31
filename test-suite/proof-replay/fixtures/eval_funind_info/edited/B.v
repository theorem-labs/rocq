(* Each proof reads the funind table entry of its function. In the edited
   tree h has no entry (see edited/Lib.v): [changed] must miss on that read,
   and its tactics take the second branch, as in the stock compile. g keeps
   its entry, so [same] must replay. The proofs are in their own file, so
   the counters at their start do not depend on what Function did in
   Lib.v. *)
Require Import PR.Lib.

Lemma same : forall n, g n = 0.
Proof. intro n. functional induction (g n); auto. Qed.

Lemma changed : forall n, h n = 0.
Proof. intro n. first [functional induction (h n); auto | induction n; simpl; auto]. Qed.
