(* [Ltac2 Eval] runs u outside any proof, so Ltac2 keeps the values of u
   and t (Tac2interp.GlobalValue) and compiles the body of u, whose call of
   t reads the kept value through a cell. [first] then runs u. The edited
   tree changes the body of t: [first] must miss on the ltac2_global read of
   t, and must not replay the term the old body chose. *)
From Ltac2 Require Import Ltac2.

Ltac2 t () := 1.
Ltac2 u () := t ().

Ltac2 Eval u ().

Lemma first : nat.
Proof. match Int.equal (u ()) 0 with | true => exact 0 | false => exact 1 end. Qed.
