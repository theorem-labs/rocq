(* seed uses the slot of a first probe, which closes over no section
   variable. Reset probe takes it away, and a second probe, under the same
   kernel name, closes over the section Let local_flag, whose body calls
   flag. target clears that body and takes the second probe from the cache.
   What the first probe's code reaches must not answer for the second one.
   The edited tree changes flag only: stock rejects target, and replay must
   too. *)
Definition flag : bool := true.

Definition probe (_ : unit) : bool :=
  (* The fixpoint keeps the VM from expanding probe where it is used
     (Genlambda.inlinable_body), so the use goes through probe's slot. *)
  (fix keep (n : nat) : bool := match n with O => true | S m => keep m end) O.
Eval vm_compute in (probe tt).

Lemma seed : True.
Proof.
  let b := eval vm_compute in (probe tt) in
  exact I.
Qed.

Reset probe.

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
  | _ => fail 1 "changed"
  end.
Qed.
End S.
