(* The body of the inner fixpoint below is the local definition [c] applied to
   the fixpoint. When the uniform-parameter analysis reduced that body in an
   environment that lacked the inner block's own declarations, it unfolded the
   definition one place further out, [d] (two places out for a block of two
   fixpoints), and so analysed a call that the kernel never makes. Each
   definition below then type-checks, and [russell 2] reduces to
   [russell 2 -> False], which gives a closed proof of [False]. *)

From Ltac2 Require Import Ltac2.

(* [ap_real] calls its second function argument [g2], [ap_fake] its first,
   [g1]. In the body of [inner], [g1] is [inner a] and [g2] is [inner (S a)]. *)
Definition ap_real (g1 g2 : nat -> Type) (cont : nat -> Type) (a : nat) : nat -> Type :=
  fun (m : nat) => match m with O => cont a | S k => g2 k end.
Definition ap_fake (g1 g2 : nat -> Type) (cont : nat -> Type) (a : nat) : nat -> Type :=
  fun (m : nat) => match m with O => cont a | S k => g1 k end.

Import Constr.Unsafe.

Ltac2 rec strip (n : int) (c : constr) : constr :=
  if Int.equal n 0 then c
  else match kind c with
       | Lambda _ b => strip (Int.sub n 1) b
       | _ => Control.throw (Tactic_failure (Some (Message.of_string "strip")))
       end.

(* The new body, [fun a => c (inner a) (inner (S a)) (fun x => russell x -> False) a],
   with the three de Bruijn indices given in [subst]. *)
Ltac2 mk_body (subst : constr list) :=
  let tmpl := constr:(fun (C : (nat -> Type) -> (nat -> Type) -> (nat -> Type) -> nat -> nat -> Type)
                          (I : nat -> nat -> Type) (FF : nat -> Type) =>
                        fun (a : nat) => C (I a) (I (S a)) (fun (x : nat) => FF x -> False) a) in
  substnl subst 0 (strip 3 tmpl).

(* Replace the body of the first inner fixpoint whose structural argument is
   its second one. *)
Ltac2 rec patch (subst : constr list) (c : constr) : constr :=
  match kind c with
  | Fix structs which types bodies =>
      if Int.equal (Array.get structs 0) 1
      then
        let bodies := Array.copy bodies in
        Array.set bodies 0 (mk_body subst);
        make (Fix structs which types bodies)
      else map (patch subst) c
  | _ => map (patch subst) c
  end.

(* One inner fixpoint. At the root of its body:
   inner = Rel 1, c = Rel 2, d = Rel 3, p = Rel 4, n = Rel 5, russell = Rel 6. *)
Fail Definition russell : nat -> Type :=
  ltac2:(Control.refine (fun () => patch [make (Rel 6); make (Rel 1); make (Rel 2)] constr:(
    fix russell (n : nat) {struct n} : Type :=
      match n with
      | O => True
      | S p =>
          let d := ap_fake in
          let c := ap_real in
          (fix inner (a m : nat) {struct m} : Type :=
             match m with O => True | S k => inner a k end) p p
      end))).

(* Two inner fixpoints. At the root of the first body:
   inner2 = Rel 1, inner1 = Rel 2, c = Rel 3, d1 = Rel 4, d2 = Rel 5,
   p = Rel 6, n = Rel 7, russell = Rel 8. *)
Fail Definition russell2 : nat -> Type :=
  ltac2:(Control.refine (fun () => patch [make (Rel 8); make (Rel 2); make (Rel 3)] constr:(
    fix russell (n : nat) {struct n} : Type :=
      match n with
      | O => True
      | S p =>
          let d2 := ap_fake in
          let d1 := ap_real in
          let c := ap_real in
          (fix inner1 (a m : nat) {struct m} : Type :=
             match m with O => True | S k => inner1 a k end
           with inner2 (a m : nat) {struct m} : Type :=
             match m with O => True | S k => inner2 a k end
           for inner1) p p
      end))).
