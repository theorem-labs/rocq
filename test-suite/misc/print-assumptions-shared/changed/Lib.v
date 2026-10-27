Require Import S.Base.
Axiom lib_ax : False.
Section Sec.
  Variable n : nat.
  Lemma sec_l : n = n -> base_def = 3. Proof. intros; apply base_lemma. Qed.
End Sec.
Module M <: T. Definition p := base_def. End M.
Module FM := F M.
Lemma top1 : True. Proof. pose proof (sec_l 0 eq_refl). destruct lib_ax. Qed.
Lemma empty_m : nat. Proof. exact (match lib_ax with end). Qed.
Lemma top2 : nat. Proof. pose proof FM.fl. exact (empty_m + base_def). Qed.
Lemma top3 : forest. Proof. exact (Cons Leaf Nil). Qed.
Lemma adm : 1 = 2. Admitted.
Lemma top4 : True. Proof. pose proof adm. exact I. Qed.
