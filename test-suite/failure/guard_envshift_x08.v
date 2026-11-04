(* The other half of the falsification test: identical to x07 except that the
   fake applier sits ONE local definition out (d1) instead of two (d2).
   If the environment is short by [nbodies] = 2 declarations, the analysis
   unfolds d2 (the real applier) here, sees the non-uniform call and refuses. *)

From Ltac2 Require Import Ltac2.

Definition ap_realT (g1 g2 : nat -> Type) (cont : nat -> Type) (a : nat) : nat -> Type :=
  fun (m : nat) => match m with O => cont a | S k => g2 k end.
Definition ap_fakeT (g1 g2 : nat -> Type) (cont : nat -> Type) (a : nat) : nat -> Type :=
  fun (m : nat) => match m with O => cont a | S k => g1 k end.

Import Constr.Unsafe.

Ltac2 rec strip (n : int) (c : constr) : constr :=
  if Int.equal n 0 then c
  else match kind c with
       | Lambda _ b => strip (Int.sub n 1) b
       | _ => Control.throw (Tactic_failure (Some (Message.of_string "strip")))
       end.

Ltac2 mk_body () :=
  let tmpl := constr:(fun (C : (nat -> Type) -> (nat -> Type) -> (nat -> Type) -> nat -> nat -> Type)
                          (I : nat -> nat -> Type) (FF : nat -> Type) =>
                        fun (a : nat) => C (I a) (I (S a)) (fun (x : nat) => FF x -> False) a) in
  substnl [make (Rel 8); make (Rel 2); make (Rel 3)] 0 (strip 3 tmpl).

Ltac2 rec patch (c : constr) : constr :=
  match kind c with
  | Fix structs which types bodies =>
      if Int.equal (Array.get structs 0) 1
      then make (Fix structs which types
                   (Array.of_list [mk_body (); Array.get bodies 1]))
      else map patch c
  | _ => map patch c
  end.

Fail Definition russell : nat -> Type :=
  ltac2:(Control.refine (fun () => patch constr:(
    fix russell (n : nat) {struct n} : Type :=
      match n with
      | O => True
      | S p =>
          let d2 := ap_realT in
          let d1 := ap_fakeT in
          let c := ap_realT in
          (fix inner1 (a m : nat) {struct m} : Type :=
             match m with O => True | S k => inner1 a k end
           with inner2 (a m : nat) {struct m} : Type :=
             match m with O => True | S k => inner2 a k end
           for inner1) p p
      end))).
