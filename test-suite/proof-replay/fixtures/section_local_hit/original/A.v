(* l unfolds c, a constant of the open section S: its record reads c by its
   kernel name (PR.A.c), which the nametab binds only under the section path
   (PR.A.S.c) while S is open. Replay must look it up there and replay l; the
   edit, after the section, changes nothing l read. Every evaluator that
   reads a kernel name back goes through Lib.global_of_kernel_string. No
   application under an expected type: bidirectionality_hint has no
   evaluator yet. *)
Section S.
Definition c := true.
Lemma l : c = true.
Proof. unfold c. exact eq_refl. Qed.
End S.
