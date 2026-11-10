(* The answer's statement file drops the challenge's own constraint and
   asserts its opposite. Every declaration still compares equal -- a
   Constraint declares nothing -- so only the graphs differ: the challenge
   stands on u < v and this answer does not, and could not, since it stands
   on v <= u. The union of the two graphs has a cycle.

   This is the direction that must never be dropped: because the kernel
   checked the answer, its graph alone is consistent, so a cycle against the
   challenge shows up here and nowhere else. *)

Monomorphic Universe u.
Monomorphic Universe v.
Monomorphic Universe p.
Monomorphic Universe q.

Monomorphic Constraint v <= u.

Monomorphic Definition su : Type@{u} := nat.
Monomorphic Definition sv : Type@{v} := bool.
Monomorphic Definition sp : Type@{p} := unit.
Monomorphic Definition sq : Type@{q} := bool.

Monomorphic Definition rel (A : Type@{p}) (B : Type@{q}) : Prop := True.

Theorem thm : rel sp sq.
Proof. exact I. Qed.
