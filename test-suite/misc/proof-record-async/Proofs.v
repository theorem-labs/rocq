(* misc/proof-record-async.sh compiles this file with -proof-record twice: once
   as an ordinary compile, once with -async-proofs on. Two opaque proofs, so
   the driver can require the SAME entries in both records. *)

Lemma first : 10 * 10 = 100.
Proof. reflexivity. Qed.

Lemma second : forall n : nat, n + 0 = n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
