Require Import Ltac2.Ltac2.

(** The interpreter computes an application of a pure primitive (one defined with [ret] or [eret] in
    Tac2externals) directly when it runs it. Each test below gives the value that the general path
    gives, in each position where the direct path is taken: the tail of a function, the right-hand
    side of a let, the scrutinee of a match, and an argument. *)

Ltac2 check (b : bool) := if b then () else Control.throw (Invalid_argument None).
Ltac2 check_int (n : int) (m : int) := check (Int.equal n m).

(** Argument order and values. *)
Ltac2 tail_sub () := Int.sub 10 3.
Ltac2 let_sub () := let x := Int.sub 10 3 in Int.add x 1.
Ltac2 match_eq (x : int) := match Int.equal x 7 with true => 1 | false => 0 end.
Ltac2 add3 (a : int) (b : int) (c : int) := Int.sub a (Int.add b c).
Ltac2 nested () := add3 (Int.sub 20 3) (Int.mul 2 3) 1.
Ltac2 cmp (x : int) (y : int) := Int.compare x y.

Ltac2 Eval check_int (tail_sub ()) 7.
Ltac2 Eval check_int (let_sub ()) 8.
Ltac2 Eval check_int (match_eq 7) 1.
Ltac2 Eval check_int (match_eq 8) 0.
Ltac2 Eval check_int (nested ()) 10.
Ltac2 Eval check (Int.lt (cmp 1 2) 0).
Ltac2 Eval check (Int.gt (cmp 2 1) 0).

(** A primitive applied to fewer arguments than it takes gives a closure. *)
Ltac2 partial () := let f := Int.add 1 in f 2.
Ltac2 Eval check_int (partial ()) 3.

(** Arguments run from left to right: the first one writes a field that the second one reads. *)
Ltac2 Type rr := { mutable c : int }.
Ltac2 two (a : int) (b : int) := Int.add (Int.mul a 10) b.
Ltac2 order () :=
  let r := { c := 0 } in
  two (r.(c) := 1; 0) (Int.add (r.(c)) 1).
Ltac2 Eval check_int (order ()) 2.

(** The same in a match scrutinee and a let: the primitive reads the field after the write. *)
Ltac2 after_write () :=
  let r := { c := 0 } in
  let _ := (r.(c) := 4) in
  let y := Int.add (r.(c)) 1 in
  match Int.equal (r.(c)) 4 with true => y | false => 0 end.
Ltac2 Eval check_int (after_write ()) 5.

(** A primitive that reads the evar map (Constr.Unsafe.kind) sees the evar map of the moment it
    runs, here after a tactic instantiated the evar. *)
Ltac2 is_evar (c : constr) := match Constr.Unsafe.kind c with Constr.Unsafe.Evar _ _ => true | _ => false end.
Goal exists n : nat, n = 0.
Proof.
  eexists.
  let lhs := match Constr.Unsafe.kind (Control.goal ()) with
             | Constr.Unsafe.App _ args => Array.get args 1
             | _ => Control.throw (Invalid_argument None)
             end in
  check (is_evar lhs);
  exact eq_refl;
  check (match is_evar lhs with true => false | false => true end).
Qed.

(** Pure primitives in the continuation of a tactic with two successes run once per success: the
    continuation runs with x = 1, fails, and runs again with x = 2. *)
Ltac2 count_runs () :=
  let r := { c := 0 } in
  let x := Control.plus (fun () => 1) (fun _ => 2) in
  r.(c) := Int.add (r.(c)) x;
  match Int.equal x 1 with
  | true => Control.zero (Invalid_argument None)
  | false => r.(c)
  end.
Ltac2 Eval check_int (count_runs ()) 3.

(** With backtraces or Ltac2-in-Ltac1 profiling on, a primitive's frame must be pushed, so the
    general path runs; the values are the same. *)
Set Ltac2 Backtrace.
Ltac2 Eval check_int (nested ()) 10.
Ltac2 Eval check_int (order ()) 2.
Ltac2 Eval check_int (count_runs ()) 3.
Unset Ltac2 Backtrace.
Set Ltac2 In Ltac1 Profiling.
Ltac2 Eval check_int (nested ()) 10.
Ltac2 Eval check_int (partial ()) 3.
Ltac2 Eval check_int (after_write ()) 5.
Unset Ltac2 In Ltac1 Profiling.
