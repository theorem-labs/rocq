(* C3 probe, second attempt: the bare occurrence is handed to an applier that
   DISCARDS it.  The applier's first function argument [g] is never used, so
   after split_struct_arg's whd_all the bare occurrence is gone from the term
   find_uniform_parameters analyses, while it is still there in the original
   body that drop_uniform_parameters rewrites.  The analysis measures a
   uniform prefix of 1 from the applied occurrence [h k] = [inner a k], and
   drop_uniform_parameters then asks List.skipn to drop one argument from the
   bare occurrence's empty argument list. *)

From Ltac2 Require Import Ltac2.

Definition ap_mix (g : nat -> nat -> nat) (h : nat -> nat) (cont : nat -> nat)
                  (a : nat) : nat -> nat :=
  fun (m : nat) => match m with O => cont a | S k => h k end.

Import Constr.Unsafe.

Ltac2 rec strip (n : int) (c : constr) : constr :=
  if Int.equal n 0 then c
  else match kind c with
       | Lambda _ b => strip (Int.sub n 1) b
       | _ => Control.throw (Tactic_failure (Some (Message.of_string "strip")))
       end.

Ltac2 mk_body () :=
  let tmpl := constr:(fun (C : (nat -> nat -> nat) -> (nat -> nat) -> (nat -> nat) -> nat -> nat -> nat)
                          (I : nat -> nat -> nat) (FF : nat -> nat) =>
                        fun (a : nat) => C I (I a) (fun (x : nat) => S (FF x)) a) in
  substnl [make (Rel 6); make (Rel 1); make (Rel 2)] 0 (strip 3 tmpl).

Ltac2 rec patch (c : constr) : constr :=
  match kind c with
  | Fix structs which types _bodies =>
      if Int.equal (Array.get structs 0) 1
      then make (Fix structs which types (Array.of_list [mk_body ()]))
      else map patch c
  | _ => map patch c
  end.

Fail Definition F : nat -> nat :=
  ltac2:(Control.refine (fun () => patch constr:(
    fix F (n : nat) {struct n} : nat :=
      match n with
      | O => O
      | S p =>
          let d := ap_mix in
          let c := ap_mix in
          (fix inner (a m : nat) {struct m} : nat :=
             match m with O => O | S k => inner a k end) p p
      end))).
