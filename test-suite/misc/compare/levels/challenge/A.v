(* Two monomorphic levels, i and j, with i <= j. *)

Monomorphic Definition f@{i j} (X : Type@{i}) : Type@{j} := X.

Theorem thm : forall n : nat, n = n.
Proof.
Admitted.
