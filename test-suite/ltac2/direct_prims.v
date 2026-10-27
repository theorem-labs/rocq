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

(** Exceptions in the arguments of a pure primitive: the effects of the arguments before the one
    that fails happen, the arguments after it and the primitive do not run, and the handler sees
    the exception of the failure. (Fatal exceptions, [Control.throw], are in
    output/ltac2_direct_prims_bt.v and output/ltac2_direct_prims_exn.v.) *)
Ltac2 Type exn ::= [ E1 | E2 (int) ].
Ltac2 caught (f : unit -> int) : int :=
  Control.plus f (fun e => match e with E1 => -1 | E2 n => Int.neg n | _ => Control.throw e end).

Ltac2 Eval
  let r := { c := 0 } in
  check_int (caught (fun () => Int.add (r.(c) := 1; 0) (Control.zero E1))) -1;
  check_int (r.(c)) 1.
Ltac2 Eval
  let r := { c := 0 } in
  check_int (caught (fun () => Int.add (Control.zero (E2 5)) (r.(c) := 1; 0))) -5;
  check_int (r.(c)) 0.
Ltac2 Eval check_int (caught (fun () => let x := Int.sub 1 (Control.zero (E2 3)) in Int.add x 1)) -3.
Ltac2 Eval check_int (caught (fun () => match Int.equal (Control.zero E1) 0 with true => 1 | false => 2 end)) -1.

(** Backtracking: a pure primitive applied to a value with two successes. The code after it
    resumes at the second success, in a let, in a match scrutinee, and in [Control.case]; under
    [Control.once] it does not resume. *)
Ltac2 Eval
  let r := { c := 0 } in
  let v := Control.plus
    (fun () => let x := Int.add (Control.plus (fun () => 1) (fun _ => 2)) 10 in
               r.(c) := Int.add (r.(c)) 1;
               match Int.equal x 11 with true => Control.zero E1 | false => x end)
    (fun _ => 0) in
  check_int v 12; check_int (r.(c)) 2.
Ltac2 Eval
  check_int (Control.plus
    (fun () => match Int.equal (Control.plus (fun () => 1) (fun _ => 2)) 2 with
               | true => 9 | false => Control.zero E1 end)
    (fun _ => 0)) 9.
Ltac2 Eval
  match Control.case (fun () => Int.mul (Control.plus (fun () => 2) (fun _ => 3)) 10) with
  | Val p =>
    let (v, k) := p in
    check_int v 20;
    match Control.case (fun () => k E1) with
    | Val p =>
      let (v, k) := p in
      check_int v 30;
      match Control.case (fun () => k (E2 4)) with
      | Val _ => check false
      | Err e => match e with E2 n => check_int n 4 | _ => check false end
      end
    | Err _ => check false
    end
  | Err _ => check false
  end.
Ltac2 Eval
  check_int (Control.plus
    (fun () => let x := Control.once (fun () => Int.add (Control.plus (fun () => 1) (fun _ => 2)) 0) in
               match Int.equal x 1 with true => Control.zero E1 | false => x end)
    (fun _ => 5)) 5.

(** [Control.enter], [Control.focus] and [Control.zero] with goals. [Control.enter] builds the
    tactic of its body once and runs it in each goal, so a pure primitive in the first step of the
    body (the right-hand side of a let, a match scrutinee) runs once per goal, in goal order, and
    reads the state of that run: a field the previous goal's run wrote, and that goal. A failure in
    an argument fails that goal's run and leaves the goals as they were. *)
Ltac2 goal_args () := match Constr.Unsafe.kind (Control.goal ()) with
                      | Constr.Unsafe.App _ args => Array.length args
                      | _ => 0
                      end.
Goal True /\ 2 = 2.
Proof.
  split.
  all: let r := { c := 0 } in
  Control.enter (fun () => r.(c) := Int.add (Int.mul (r.(c)) 10) (Int.add (goal_args ()) 1));
  check_int (r.(c)) 14.
  all: check_int (Control.focus 2 2 (fun () => goal_args ())) 3.
  all: let r := { c := 0 } in
  Control.enter (fun () => let x := Int.add (r.(c)) 1 in r.(c) := x);
  check_int (r.(c)) 2.
  all: let r := { c := 0 } in
  Control.enter (fun () => match Int.equal (r.(c)) 0 with
                           | true => r.(c) := 10
                           | false => r.(c) := Int.add (r.(c)) 1
                           end);
  check_int (r.(c)) 11.
  all: let r := { c := 0 } in
  Control.enter (fun () => let n := goal_args () in r.(c) := Int.add (Int.mul (r.(c)) 10) n);
  check_int (r.(c)) 3.
  all: let r := { c := 0 } in
  Control.enter (fun () => r.(c) := Int.add (r.(c))
                   (Control.plus (fun () => Int.add (Control.zero E1) 1) (fun _ => 1)));
  check_int (r.(c)) 2.
  all: check_int (Control.plus (fun () => Control.enter (fun () => let _ := Int.add (Control.zero (E2 4)) 1 in ()); 0)
                          (fun e => match e with E2 n => n | _ => 0 end)) 4.
  all: check_int (Control.numgoals ()) 2.
  Control.focus 1 1 (fun () => exact I).
  reflexivity.
Qed.

(** Effects between a call and its arguments: the head is evaluated before the arguments, and an
    argument's tactic effect (instantiating an evar) happens before the primitive reads the evar
    map. *)
Ltac2 Eval let r := { c := 0 } in check_int ((let _ := (r.(c) := 5) in Int.add) (r.(c)) 1) 6.
Goal exists n : nat, n = 0.
Proof.
  eexists.
  let lhs := match Constr.Unsafe.kind (Control.goal ()) with
             | Constr.Unsafe.App _ args => Array.get args 1
             | _ => Control.throw (Invalid_argument None)
             end in
  check (match Constr.Unsafe.kind (exact eq_refl; lhs) with Constr.Unsafe.Evar _ _ => false | _ => true end).
Qed.
