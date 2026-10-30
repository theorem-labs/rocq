(* The edited tree adds the constant moved before the others, so every later
   constant's bytecode moves in the library's code table. Its bytecode and
   the constants it calls do not change, so every proof that runs it with
   vm_compute must still replay. *)
Definition other : nat := 0.
Definition moved : nat := 1.
Definition flag : bool := true.
Register Inline flag.
Definition probe (_ : unit) : bool := flag.
Definition flag2 : bool := true.
Definition probe2 (_ : unit) : bool := flag2.

Lemma same_file : True.
Proof.
  let b := eval vm_compute in (probe2 tt) in
  lazymatch b with
  | true => exact I
  | false => fail 1 "changed"
  end.
Qed.
