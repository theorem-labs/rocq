(* One level where the challenge has two: the map would have to send both
   of the challenge's levels to it, which is not a bijection. *)

Monomorphic Definition f@{i} (X : Type@{i}) : Type@{i} := X.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.
