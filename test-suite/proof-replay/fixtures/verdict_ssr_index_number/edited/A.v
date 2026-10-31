(* ssreflect reads the count of [do k! split] from the term k by printing it
   back as a number: the number notation for nat in the most recently opened
   scope decides the count. The edited tree declares that notation with a
   printer that gives 1 for every nat, so the count is 1, not 2, and the stock
   script fails. Replay must fail too: no other read of the proof sees the
   printer (gate review, breadth audit gap BA6). *)
From Corelib Require Import ssreflect.

Declare Scope my_scope.
Definition my_to_uint (n : nat) : Number.uint :=
  Number.UIntDecimal (Decimal.D1 Decimal.Nil).
Number Notation nat Nat.of_num_uint my_to_uint : my_scope.
Open Scope my_scope.

Lemma p : True /\ True /\ True.
Proof.
  let k := constr:(S (S O)) in do k! split.
  all: exact I.
Qed.
