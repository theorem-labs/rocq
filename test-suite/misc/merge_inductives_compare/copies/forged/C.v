Require MergeTest.A MergeTest.B.

(* Another statement under the task's name: it must fail. *)
Theorem thm : MergeTest.A.flip MergeTest.B.red = MergeTest.A.flip MergeTest.B.red.
Proof. reflexivity. Qed.
