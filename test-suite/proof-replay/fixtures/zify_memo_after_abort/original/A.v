From Stdlib Require Import ZArith Lia.

(* The aborted goal runs zify's translation and injection first; the lemma
   then asks for the same ones with the global environment unchanged. *)
Goal forall a b c d e : nat,
  a + 3 * b + 5 * c + 7 * d + 11 * e <= 100 -> a + 3 * b + 5 * c + 7 * d + 11 * e <= 101.
Proof. intros; lia. Abort.

Lemma memo : forall a b c d e : nat,
  a + 3 * b + 5 * c + 7 * d + 11 * e <= 100 -> a + 3 * b + 5 * c + 7 * d + 11 * e <= 101.
Proof. intros; lia. Qed.
