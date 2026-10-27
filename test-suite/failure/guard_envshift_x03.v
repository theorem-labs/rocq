(* C1 probe, closed proof of False.  Same mechanism as x02, Type-valued so
   that the contradiction is a one-step conversion (the shape of
   rocq-prover/rocq#22382's exploit): russell 2 == (russell 2 -> False). *)

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

(* At the root of the inner body:
   inner = Rel 1, c = Rel 2, d = Rel 3, p = Rel 4, n = Rel 5, russell = Rel 6. *)
Ltac2 mk_body () :=
  let tmpl := constr:(fun (C : (nat -> Type) -> (nat -> Type) -> (nat -> Type) -> nat -> nat -> Type)
                          (I : nat -> nat -> Type) (FF : nat -> Type) =>
                        fun (a : nat) => C (I a) (I (S a)) (fun (x : nat) => FF x -> False) a) in
  substnl [make (Rel 6); make (Rel 1); make (Rel 2)] 0 (strip 3 tmpl).

Ltac2 rec patch (c : constr) : constr :=
  match kind c with
  | Fix structs which types bodies =>
      if Int.equal (Array.get structs 0) 1
      then make (Fix structs which types (Array.of_list [mk_body ()]))
      else map patch c
  | _ => map patch c
  end.

Fail Definition russell : nat -> Type :=
  ltac2:(Control.refine (fun () => patch constr:(
    fix russell (n : nat) {struct n} : Type :=
      match n with
      | O => True
      | S p =>
          let d := ap_fakeT in
          let c := ap_realT in
          (fix inner (a m : nat) {struct m} : Type :=
             match m with O => True | S k => inner a k end) p p
      end))).
