(* target asks Ltac2 for the fields of the module being compiled, which is
   open, and asserts that it has none. The edited tree declares one
   definition before target and changes nothing in target's key: not its
   statement, its sentences or its position. Stock now fails the assertion,
   so replay must not install the stored term (cross-model soundness review
   of 777213df6e, finding 1). *)
From Ltac2 Require Import Ltac2.

Lemma target : True.
Proof.
  let fields := Option.get (Module.module_contents (Module.current_module ())) in
  Control.assert_true (Int.equal (List.length fields) 0).
  exact I.
Qed.
