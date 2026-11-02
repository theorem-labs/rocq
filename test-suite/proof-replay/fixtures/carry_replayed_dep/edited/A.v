(* The carry-over case (GRADE, through R1P3, 2026-10-25): a grade REUSES one
   registered object and REPLAYS the object it was compiled against.

   `p`'s statement elaborates a fresh universe level, which is the proof shape
   whose replayed object has stock's value but not stock's Marshal sharing.
   B.vo records a digest of A.vo, so B.vo only loads beside the replayed A.vo
   when the replayed object is the bytes stock would have written. *)
Lemma p : forall A : Type, A -> A.
Proof. intros A x. exact x. Qed.
