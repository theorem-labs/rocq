(* A mutual inner block where one member's RAW binder prefix calls its
   SIBLING, with no let in sight. The analysis looks at each body's
   references to itself, so a call between siblings was never measured. *)
Fail Fixpoint outer_sib (n : nat) {struct n} : nat :=
  match n with
  | O => O
  | S p =>
      (fix a (q : nat := b p O) (x m : nat) {struct m} : nat :=
         match m with O => outer_sib x | S k => a x k end
       with b (x m : nat) {struct m} : nat :=
         match m with O => outer_sib x | S k => b x k end
       for a) p p
  end.
