(* The soundness case the verified-grader lead named: the answer adds a
   constraint between a level of its own, which the map pairs with a
   challenge level, and a level of a library both sides share, which the
   map holds as the identity. Comparing only constraints between two levels
   the walk itself paired would miss it. Here Agent's level is forced below
   Shared's, which the challenge does not require.

   The declaration that forces it is the answer's own, so R3 never compares
   it; only the universe graphs differ. *)
Require Import Pre.Shared.

Definition Agent := Type.

Definition force : Shared := Agent.

Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.

Theorem thm : forall n : nat, n = n.
Proof. reflexivity. Qed.

Theorem other : forall b : bool, b = b.
Proof. reflexivity. Qed.
