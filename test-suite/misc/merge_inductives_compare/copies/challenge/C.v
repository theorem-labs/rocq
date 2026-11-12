Require MergeTest.A MergeTest.B.

(* [MergeTest.B.red] is a [MergeTest.B.colour] and [MergeTest.A.flip] takes a
   [MergeTest.A.colour]: the statement type-checks only once the two copies
   are one type. *)
Theorem thm : MergeTest.A.flip (MergeTest.A.flip MergeTest.B.red) = MergeTest.B.red.
Proof. Admitted.
