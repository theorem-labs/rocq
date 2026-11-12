Require MergeTest.A MergeTest.B.

Theorem thm : MergeTest.A.flip (MergeTest.A.flip MergeTest.B.red) = MergeTest.B.red.
Proof. reflexivity. Qed.
