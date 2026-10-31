(* The Eval fills the VM cache with probe's value, which holds flag's value
   through the section Let local_flag. target clears local_flag's body
   before it runs probe from the cache, so the current environment no longer
   leads from probe to flag. The edited tree changes flag only: stock
   rejects target, and replay must too. *)
Definition flag : bool := false.

Section S.
Let local_flag : bool := flag.
Definition probe (_ : unit) : bool :=
  (* The fixpoint keeps the VM from expanding probe where it is used
     (Genlambda.inlinable_body), so the use goes through probe's slot. *)
  (fix keep (n : nat) : bool := match n with O => local_flag | S m => keep m end) O.

Eval vm_compute in (probe tt).

Lemma target : True.
Proof.
  clearbody local_flag.
  let b := eval vm_compute in (probe tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.
End S.
