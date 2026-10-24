(* -*- coqchk-prog-args: ("-native-conversion" "yes" "-native-conversion-after" "0") -*- *)

(* coqchk decides this VM cast with native code. The code of the cast
   defines A_B.c and A.B_c together, so their OCaml names must differ:
   with module path and label joined by "_", both names would end in
   "A_B_c", the second definition would hide the first, and the cast would
   compare (false, false) with (true, false). *)
Module A_B.
  Definition c := true.
End A_B.

Module A.
  Definition B_c := false.
End A.

Lemma names_differ : (A_B.c, A.B_c) = (true, false).
Proof. vm_cast_no_check (eq_refl (true, false)). Qed.
