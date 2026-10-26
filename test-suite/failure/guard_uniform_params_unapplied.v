(* In each definition below, an inner fixpoint occurs as an argument without
   being applied. The guard checker used to stop on each of them with
   Anomaly "Uncaught exception Failure("List.skipn")". *)

(* [inner] is passed unapplied to the let-bound [invoke]. An unapplied
   occurrence allows no uniform prefix, so [a] is not known to be smaller
   than [n] and the call [outer a] is refused. *)
Fail Fixpoint outer (n : nat) : nat :=
  match n with
  | O => O
  | S p =>
      let invoke := fun (h : nat -> nat -> nat) (a m : nat) => h a m in
      (fix inner (a m : nat) {struct m} : nat :=
         match m with
         | O => outer a
         | S k => invoke inner a k
         end) p p
  end.

(* The same with [app], bound inside the inner body. This definition would
   give [f (C L) : False]. *)
Inductive T : Set := C : T -> T | L : T.
Definition P (t : T) : Type := match t with L => unit | C _ => False end.
Definition R (u : T) (k : nat) : Type := match k with O => P u | S _ => False end.
Fail Fixpoint f (t : T) : P t :=
  match t as t0 return P t0 with
  | L => tt
  | C t' =>
      (fix g (u : T) (k : nat) {struct k} : R u k :=
         match k as k0 return R u k0 with
         | O => f u
         | S k' =>
             let app := fun h : forall (u : T) (k : nat), R u k => h (C t') k' in
             match k' as k0 return (R (C t') k0 -> False) with
             | O => fun x => x
             | S _ => fun x => x
             end (app g)
         end) t' (S O)
  end.

(* In a block of two fixpoints, [inner2] is passed unapplied to [invoke] in
   the body of [inner1]. *)
Fail Fixpoint outer_mutual (n : nat) : nat :=
  match n with
  | O => O
  | S p =>
      let invoke := fun (h : nat -> nat -> nat) (a m : nat) => h a m in
      (fix inner1 (a m : nat) {struct m} : nat :=
         match m with
         | O => outer_mutual a
         | S k => invoke inner2 a k
         end
       with inner2 (a m : nat) {struct m} : nat :=
         match m with
         | O => outer_mutual a
         | S k => inner1 a k
         end
       for inner1) p p
  end.

(* The body of [inner] is the local definition [c] applied to [inner] itself
   and to [inner a]. [c] ignores its first argument, so the reduction that the
   uniform-parameter analysis performs removes the unapplied occurrence, and
   only the rewriting of the body meets it. *)
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

(* [fun a => c inner (inner a) (fun x => S (F x)) a]. At the root of the body:
   inner = Rel 1, c = Rel 2, d = Rel 3, p = Rel 4, n = Rel 5, F = Rel 6. *)
Ltac2 mk_body () :=
  let tmpl := constr:(fun (C : (nat -> nat -> nat) -> (nat -> nat) -> (nat -> nat) -> nat -> nat -> nat)
                          (I : nat -> nat -> nat) (FF : nat -> nat) =>
                        fun (a : nat) => C I (I a) (fun (x : nat) => S (FF x)) a) in
  substnl [make (Rel 6); make (Rel 1); make (Rel 2)] 0 (strip 3 tmpl).

Ltac2 rec patch (c : constr) : constr :=
  match kind c with
  | Fix structs which types _ =>
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
