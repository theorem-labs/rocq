(* A mutual INNER block where one member's raw binder prefix holds a call to
   its SIBLING. The analysis looks at each body's references to itself, so a
   call between siblings was never measured.

   The block is built through the tactic path on purpose. In a
   `fix a … with b … for a` TERM the sibling is not in scope inside an
   earlier member's binder list, so written that way the file dies at
   elaboration ("The reference b was not found in the current environment")
   and the Fail below would succeed without the kernel ever seeing the term.
   With `fix … with …` as a tactic both members are in scope, and `pose`
   before `intros` puts the dead definition in the binder prefix of [a].

   The 9.3 base (release/2026-10-25 d66271245d) accepts this definition;
   with this commit it is refused, "Recursive definition of a is ill-formed."
   The companion success/guard_prefix_sibling_control.v is the same block
   with a prefix definition that mentions nothing recursive, and stays
   accepted. *)
Definition outer_sib : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix a 2 with (b (x m : nat) {struct m} : nat).
    + pose (dead := b p O).
      intros x m.
      destruct m as [|k].
      * exact (outer x).
      * exact (a x k).
    + intros x m.
      destruct m as [|k].
      * exact (outer x).
      * exact (b x k).
  Fail Defined.
Abort.
