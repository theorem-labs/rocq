(* An axiom declared inside an opaquely sealed module is reached by the
   sealed proof through a helper that lives only in the implementation. The
   environment holds the interface alone, so the summary can only see the
   axiom if the checker records what it checked. Both helper forms, opaque
   and transparent, must list the axiom; the third module is the control the
   release checker already lists. *)

Module Type T. Parameter tgt : 1 = 2. End T.

Module OpaqueHelper : T.
  Axiom ax : False.
  Lemma helper : False. Proof. exact ax. Qed.
  Lemma tgt : 1 = 2. Proof. destruct helper. Qed.
End OpaqueHelper.

Module TransparentHelper : T.
  Axiom ax : False.
  Definition helper : False := ax.
  Lemma tgt : 1 = 2. Proof. destruct helper. Qed.
End TransparentHelper.

Module Direct : T.
  Axiom ax : False.
  Lemma tgt : 1 = 2. Proof. destruct ax. Qed.
End Direct.

(* A module the sealed implementation declares is hidden with it, whether it
   is a plain module or one only declared. Print Assumptions names
   Nested.Plain.inner_ax for the proof below and the summary names it the
   same way; Nested.Declared.n is listed because it is declared, which is
   what the environment fold does with a visible one. *)
Module Type S. Parameter n : nat. End S.

Module Nested : T.
  Module Plain.
    Axiom inner_ax : False.
  End Plain.
  Declare Module Declared : S.
  Definition used := Declared.n.
  Lemma helper : False. Proof. exact Plain.inner_ax. Qed.
  Lemma tgt : 1 = 2. Proof. destruct helper. Qed.
End Nested.
