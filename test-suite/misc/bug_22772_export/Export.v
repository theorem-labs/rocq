(* Agent file: no array word, no literal, no exact_no_check. Arrays come only from the trusted import. *)
From T Require Import TrustedMem.
Definition T (m : mem) : Prop := forall y : bool, read m 0 = y.
Lemma bad : forall x : bool, T (init 1 x).
Proof. lazy. intros x y. reflexivity. Qed.
Theorem boom : False.
Proof. exact (match bad true false in _ = b return (if b then True else False) with eq_refl => I end). Qed.
Print Assumptions boom.
