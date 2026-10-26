(* The base db rewrites with fg from left to right here and, in the edited
   tree, from right to left: same lemma, same hint count, so neither the
   constant read nor the hint counter moves, and both proofs still close, with
   another term. lstrat reaches the base through rewrite_strat's hints
   strategy (Autorewrite.find_matches), lauto through autorewrite
   (find_rewrites); both must miss on the autorewrite read. control reads no
   base and hits. No numerals: their recorded interpretation holds their
   source position. *)
Require Import Setoid.

Parameter f g : nat -> nat.
Axiom fg : forall n, f n = g n.

Create Rewrite HintDb db.
#[export] Hint Rewrite <- fg : db.

Lemma lstrat : forall n, f n = g n.
Proof. intro n. rewrite_strat (topdown (hints db)). reflexivity. Qed.

Lemma lauto : forall n, f n = g n.
Proof. intro n. autorewrite with db. reflexivity. Qed.

Lemma control : True.
Proof. exact I. Qed.
