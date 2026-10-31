(* functional induction looks f up in the funind table to find f_ind. In the
   edited tree f has no entry (see edited/Lib.v), so the stock script fails
   with "Cannot find induction information on f", and the replay compile must
   fail too. The proof is in its own file, so the counters at its start do
   not depend on what Function did in Lib.v. *)
Require Import PR.Lib.

Lemma p : forall n, f n = 0.
Proof. intro n. functional induction (f n); auto. Qed.
