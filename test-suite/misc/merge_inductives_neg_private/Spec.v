Private Inductive pos : Type := mk : nat -> pos.
(* A quotient: consistent while nobody outside this file can match on pos. *)
Axiom pos_irr : forall n m : nat, mk n = mk m.
