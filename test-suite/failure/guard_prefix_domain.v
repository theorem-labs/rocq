(* An occurrence of the inner fixpoint in the TYPE of one of its own prefix
   binders. [split_struct_arg] keeps that type in the context it returns, and
   [inductive_of_mutfix] then raised the kernel anomaly "Bad occurrence of
   recursive call" on it, which [Fail] does not catch. The raw-prefix rule in
   [check_fix_pre_sorts] runs before [inductive_of_mutfix] and refuses the
   definition with an ordinary guard error. (breaka/D5.v of
   dispatch://BET-241.) *)
Definition outerD5 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (fun (a : (fun _ : nat -> nat -> nat => nat) inner) (m : nat) => _).
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
    Fail Defined.
Abort.
