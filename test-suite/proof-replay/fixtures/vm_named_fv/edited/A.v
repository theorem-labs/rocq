(* probe closes over the section variable local_flag, whose body calls
   flag. The Eval fills the VM cache with probe's value, which holds flag's
   value through local_flag; probe's code names no global. The edited tree
   changes flag only, so stock rejects target, and replay must too. *)
Definition flag : bool := false.

Section S.
Let local_flag : bool := flag.
Definition probe (_ : unit) : bool := local_flag.

Eval vm_compute in (probe tt).

Lemma target : True.
Proof.
  let b := eval vm_compute in (probe tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.
End S.
