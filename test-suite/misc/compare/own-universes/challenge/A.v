(* The task's OWN universes: the statements stand on them, so what an answer
   says about them is a claim about the task. The challenge orders u below v
   and leaves p and q apart. *)

Monomorphic Universe u.
Monomorphic Universe v.
Monomorphic Universe p.
Monomorphic Universe q.

Monomorphic Constraint u < v.

Monomorphic Definition su : Type@{u} := nat.
Monomorphic Definition sv : Type@{v} := bool.
Monomorphic Definition sp : Type@{p} := unit.
Monomorphic Definition sq : Type@{q} := bool.

Monomorphic Definition rel (A : Type@{p}) (B : Type@{q}) : Prop := True.

Theorem thm : rel sp sq.
Proof.
Admitted.
