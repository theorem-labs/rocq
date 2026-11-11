(* P, Q and R are constants, so all three are set aside before X maps d.
   R then decides c, Q decides b from c, and P decides a from b.  Only the
   visit order R, Q, P would decide all three in one retry pass; these
   names give another order, so the retry must repeat. *)
Unset Elimination Schemes.

Monomorphic Universes a b c d.

Definition P : Type@{max(a,b)} -> nat := fun _ => 0.
Definition Q : Type@{max(b,c)} -> nat := fun _ => 0.
Definition R : Type@{max(c,d)} -> nat := fun _ => 0.

Inductive X : Type@{d} := cx.

Theorem thm : forall n : nat, n = n.
Proof.
Admitted.
