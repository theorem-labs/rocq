(* In a block of two fixpoints, [inner2] is passed unapplied to [invoke] in
   the body of [inner1]. The calls to [outer] are on [p], so the definition
   terminates, and the guard checker must not fail on the unapplied
   occurrence. *)
Fixpoint outer (n : nat) : nat :=
  match n with
  | O => O
  | S p =>
      let invoke := fun (h : nat -> nat -> nat) (a m : nat) => h a m in
      (fix inner1 (a m : nat) {struct m} : nat :=
         match m with
         | O => outer p
         | S k => invoke inner2 a k
         end
       with inner2 (a m : nat) {struct m} : nat :=
         match m with
         | O => outer p
         | S k => inner1 a k
         end
       for inner1) p p
  end.

Check eq_refl : outer 3 = 0.

(* The body of [inner] is the local definition [c] applied to [inner] itself,
   unapplied, and to [inner a]. [c] ignores its first argument. The call to
   [F] is on [p], so the definition terminates: [F (S p) = S (F p)]. Rocq 9.2.0
   accepts it, and the guard checker must not fail on the unapplied
   occurrence. *)
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

(* [fun a => c inner (inner a) (fun x => S (F p)) a]. At the root of the body:
   inner = Rel 1, c = Rel 2, d = Rel 3, p = Rel 4, n = Rel 5, F = Rel 6. *)
Ltac2 mk_body () :=
  let tmpl := constr:(fun (C : (nat -> nat -> nat) -> (nat -> nat) -> (nat -> nat) -> nat -> nat -> nat)
                          (I : nat -> nat -> nat) (FF : nat -> nat) (P : nat) =>
                        fun (a : nat) => C I (I a) (fun (x : nat) => S (FF P)) a) in
  substnl [make (Rel 4); make (Rel 6); make (Rel 1); make (Rel 2)] 0 (strip 4 tmpl).

Ltac2 rec patch (c : constr) : constr :=
  match kind c with
  | Fix structs which types _ =>
      if Int.equal (Array.get structs 0) 1
      then make (Fix structs which types (Array.of_list [mk_body ()]))
      else map patch c
  | _ => map patch c
  end.

Definition F : nat -> nat :=
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

Check eq_refl : F 3 = 3.
