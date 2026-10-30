(* probe closes over the section Let local_flag. No command fills the VM
   cache before target, so target fills probe's slot itself. A replay of
   target would leave the slot empty for the commands after it, where stock
   leaves it filled (vm_section_closure_creator), so target is not replayed
   although nothing it reads changes. *)
Definition flag : bool := true.

Section S.
Let local_flag : bool := flag.
Definition probe (_ : unit) : bool := local_flag.

Lemma target : True.
Proof.
  let b := eval vm_compute in (probe tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.
End S.
