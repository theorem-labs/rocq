(* probe closes over the section Let local_flag. No command fills the VM
   cache before target, so target fills probe's slot itself, in its own
   environment, and its reads cover what that value holds. The edited tree
   changes nothing target reads, so target replays. *)
Definition flag : bool := true.
Definition unrelated : nat := 0.

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
