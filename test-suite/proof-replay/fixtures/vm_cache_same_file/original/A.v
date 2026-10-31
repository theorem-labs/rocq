(* The same as vm_cache_lib, in one file: the Eval fills the VM cache with
   probe before target opens, the edited tree changes flag only, and target
   never looks flag up. Stock rejects target with the edited flag, so replay
   must too. *)
Definition flag : bool := true.
Definition probe (_ : unit) : bool := flag.

Eval vm_compute in (probe tt).

Lemma target : True.
Proof.
  let b := eval vm_compute in (probe tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.
