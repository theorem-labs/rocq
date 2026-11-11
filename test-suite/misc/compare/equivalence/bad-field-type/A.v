(* The negative control of the modules check: a field of the module type
   has another type in the answer. *)

Inductive word : Set := W0 | W1.

Module Type SPEC.
  Parameter step : word -> word.
  Parameter step_involutive : forall w, step w = step w.
End SPEC.

Module Ref <: SPEC.
  Definition step (w : word) : word := match w with W0 => W1 | W1 => W0 end.
  Lemma step_involutive : forall w, step w = step w.
  Proof. reflexivity. Qed.
End Ref.

Module Tgt <: SPEC.
  Definition step (w : word) : word := match w with W0 => W1 | W1 => W0 end.
  Lemma step_involutive : forall w, step w = step w.
  Proof. reflexivity. Qed.
End Tgt.

Module Equiv (A : SPEC) (B : SPEC).
  Definition agree := forall w, A.step w = B.step w.
End Equiv.

Module E := Equiv Ref Tgt.

Theorem thm : E.agree.
Proof. intro w; destruct w; reflexivity. Qed.
