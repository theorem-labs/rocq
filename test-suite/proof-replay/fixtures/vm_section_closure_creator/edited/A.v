(* warm fills probe's VM slot with a value that holds local_flag's body
   (true). later clears that body, then takes probe from the cache: stock
   gives it true, and accepts later. A replay of warm would leave the slot
   empty, so later, which runs, would fill it after the clearbody and get
   the variable instead. So warm is not replayed. Both trees are the same. *)
Definition flag : bool := true.

Section S.
Let local_flag : bool := flag.
Definition probe (_ : unit) : bool :=
  (* The fixpoint keeps the VM from expanding probe where it is used
     (Genlambda.inlinable_body), so the use goes through probe's slot. *)
  (fix keep (n : nat) : bool := match n with O => local_flag | S m => keep m end) O.

Lemma warm : True.
Proof.
  let b := eval vm_compute in (probe tt) in
  exact I.
Qed.

Lemma later : True.
Proof.
  clearbody local_flag.
  let b := eval vm_compute in (probe tt) in
  lazymatch b with
  | true => exact I
  | _ => fail 1 "different VM cache"
  end.
Qed.
End S.
