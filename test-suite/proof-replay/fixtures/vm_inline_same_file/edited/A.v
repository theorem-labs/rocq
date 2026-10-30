(* The same as vm_inline_lib, in one file: flag is inlined into probe's
   bytecode, the edited tree changes flag only, and target runs probe with
   vm_compute without looking flag up. Stock rejects target with the edited
   flag, so replay must too. *)
Definition flag : bool := false.
Register Inline flag.
Definition probe (_ : unit) : bool := flag.

Lemma target : True.
Proof.
  let b := eval vm_compute in (probe tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.
