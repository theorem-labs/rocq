Require Import Ltac2.Ltac2.

(** Once a tactic runs, the interpreter applies an Ltac2 closure to as many arguments as it takes by
    running its body at once, with the code after the call, instead of building the body's tactic
    and binding it. Each test below gives the value that building and binding gives: in each
    position of the call (the tail of a function, the right-hand side of a let, the scrutinee of a
    match, an argument), for closures that capture variables or recurse, under failures and
    backtracking, and with goals. *)

Ltac2 check (b : bool) := if b then () else Control.throw (Invalid_argument None).
Ltac2 check_int (n : int) (m : int) := check (Int.equal n m).

(** Argument order and values, in each position. *)
Ltac2 sub3 (a : int) (b : int) (c : int) := Int.sub a (Int.sub b c).
Ltac2 tail () := sub3 20 7 2.
Ltac2 in_let () := let x := sub3 20 7 2 in Int.add x 1.
Ltac2 in_match () := match sub3 20 7 2 with 15 => true | _ => false end.
Ltac2 in_arg () := sub3 (sub3 20 7 2) (sub3 9 3 1) 1.
Ltac2 Eval check_int (tail ()) 15.
Ltac2 Eval check_int (in_let ()) 16.
Ltac2 Eval check (in_match ()).
Ltac2 Eval check_int (in_arg ()) 9.

(** A match on a closure's result binds the constructor's arguments in its branch. *)
Ltac2 pair (a : int) (b : int) := (a, b).
Ltac2 swap_sub () := match pair 3 10 with (x, y) => Int.sub y x end.
Ltac2 opt (n : int) := if Int.equal n 0 then None else Some (Int.mul n 2).
Ltac2 opt_val (n : int) := match opt n with Some v => v | None => -1 end.
Ltac2 Eval check_int (swap_sub ()) 7.
Ltac2 Eval check_int (opt_val 4) 8.
Ltac2 Eval check_int (opt_val 0) -1.

(** Partial application gives a closure; a closure that returns a closure takes the rest of the
    arguments (over-application). *)
Ltac2 partial () := let f := sub3 20 in f 7 2.
Ltac2 curried (a : int) := fun b => Int.sub a b.
Ltac2 over () := curried 10 3.
Ltac2 Eval check_int (partial ()) 15.
Ltac2 Eval check_int (over ()) 7.

(** Closures see the variables of where they were made, not of where they are called; a
    parameter shadows a captured variable of the same name. The right-hand sides of one let are
    evaluated before any of its names is bound. *)
Ltac2 lexical () :=
  let x := 1 in
  let f := fun y => Int.add (Int.mul x 100) y in
  let x := 2 in
  f x.
Ltac2 shadow () := let x := 5 in let f := fun x => Int.mul x 3 in Int.add (f 7) (Int.mul x 100).
Ltac2 let_with () := let x := 1 in let x := 2 with y := x in Int.add (Int.mul x 10) y.
Ltac2 Eval check_int (lexical ()) 102.
Ltac2 Eval check_int (shadow ()) 521.
Ltac2 Eval check_int (let_with ()) 21.

(** Recursion: a recursive closure reads its own binding when it is called; mutual recursion;
    deep recursion that is not a tail call. *)
Ltac2 rec fact (n : int) := if Int.equal n 0 then 1 else Int.mul n (fact (Int.sub n 1)).
Ltac2 local_rec () :=
  let rec even n := if Int.equal n 0 then true else odd (Int.sub n 1)
  with odd n := if Int.equal n 0 then false else even (Int.sub n 1) in
  match even 10 with true => match odd 7 with true => 1 | false => 0 end | false => 0 end.
Ltac2 rec sum (n : int) := if Int.equal n 0 then 0 else Int.add n (sum (Int.sub n 1)).
Ltac2 Eval check_int (fact 10) 3628800.
Ltac2 Eval check_int (local_rec ()) 1.
Ltac2 Eval check_int (sum 100000) 5000050000.

(** Effects: the head of a call is evaluated before its arguments, the arguments from left to
    right, and the body after all of them; for a head that is not simple and a partial
    application ([order]), and for a closure applied at once to all its arguments, in each
    position ([body3]). *)
Ltac2 Type rr := { mutable c : int }.
Ltac2 log (r : rr) (d : int) := r.(c) := Int.add (Int.mul (r.(c)) 10) d.
Ltac2 body_last (r : rr) (_ : unit) (_ : unit) := log r 3.
Ltac2 order () :=
  let r := { c := 0 } in
  (log r 1; body_last r) (log r 2) (log r 4);
  r.(c).
Ltac2 Eval check_int (order ()) 1243.
Ltac2 body3 (r : rr) (_ : unit) (_ : unit) := log r 3.
Ltac2 Eval let r := { c := 0 } in body3 r (log r 2) (log r 4); check_int (r.(c)) 243.
Ltac2 Eval let r := { c := 0 } in let _ := body3 r (log r 2) (log r 4) in log r 5; check_int (r.(c)) 2435.
Ltac2 Eval let r := { c := 0 } in
  match body3 r (log r 2) (log r 4) with () => log r 6 end; check_int (r.(c)) 2436.
Ltac2 Eval let r := { c := 0 } in log r (Int.add 1 (body3 r (log r 2) (log r 4); 0)); check_int (r.(c)) 2431.

(** A closure of five or more arguments (the generic case of [Tac2val.abstract]), in each
    position, and partially applied. *)
Ltac2 five (a : int) (b : int) (c : int) (d : int) (e : int) :=
  Int.add (Int.mul a 10000) (Int.add (Int.mul b 1000) (Int.add (Int.mul c 100) (Int.add (Int.mul d 10) e))).
Ltac2 Eval check_int (five 1 2 3 4 5) 12345.
Ltac2 Eval check_int (let x := five 5 4 3 2 1 in Int.add x 1) 54322.
Ltac2 Eval check (match five 0 0 0 0 7 with 7 => true | _ => false end).
Ltac2 Eval check_int (Int.sub (five 1 1 1 1 1) (five 0 0 0 0 (Int.add 1 0))) 11110.
Ltac2 Eval check_int (let f := five 9 8 in f 7 6 5) 98765.
Ltac2 Eval let r := { c := 0 } in
  check_int (five (log r 1; 1) (log r 2; 2) (log r 3; 3) (log r 4; 4) (log r 5; 5)) 12345;
  check_int (r.(c)) 12345.

(** Failures in a closure's body: the effects before the failure happen, the code after the call
    does not run, and the handler sees the exception. *)
Ltac2 Type exn ::= [ E1 | E2 (int) ].
Ltac2 caught (f : unit -> int) : int :=
  Control.plus f (fun e => match e with E1 => -1 | E2 n => Int.neg n | _ => Control.throw e end).
Ltac2 fails_after (r : rr) (n : int) := log r 1; Control.zero (E2 n).
Ltac2 Eval
  let r := { c := 0 } in
  check_int (caught (fun () => Int.add (fails_after r 5) (log r 9; 0))) -5;
  check_int (r.(c)) 1.
Ltac2 Eval
  let r := { c := 0 } in
  check_int (caught (fun () => let x := fails_after r 3 in log r 9; x)) -3;
  check_int (r.(c)) 1.
Ltac2 Eval
  let r := { c := 0 } in
  check_int (caught (fun () => match fails_after r 4 with 0 => 0 | _ => log r 9; 1 end)) -4;
  check_int (r.(c)) 1.

(** Backtracking: a closure whose body has two successes. The code after the call resumes at the
    second success, in a let, in a match scrutinee, in an argument and through a nested call;
    under [Control.once] it does not resume. *)
Ltac2 two () := Control.plus (fun () => 1) (fun _ => 2).
Ltac2 two_deep (n : int) := if Int.equal n 0 then two () else Int.add 0 (two ()).
Ltac2 count_runs () :=
  let r := { c := 0 } in
  let x := two () in
  r.(c) := Int.add (r.(c)) x;
  match Int.equal x 1 with
  | true => Control.zero E1
  | false => r.(c)
  end.
Ltac2 Eval check_int (count_runs ()) 3.
Ltac2 Eval
  check_int (Control.plus
    (fun () => match two () with 1 => Control.zero E1 | n => Int.mul n 10 end)
    (fun _ => 0)) 20.
Ltac2 Eval
  check_int (Control.plus
    (fun () => let v := Int.add (two_deep 3) 100 in
               match Int.equal v 101 with true => Control.zero E1 | false => v end)
    (fun _ => 0)) 102.
Ltac2 Eval
  check_int (Control.plus
    (fun () => let x := Control.once (fun () => two ()) in
               match Int.equal x 1 with true => Control.zero E1 | false => x end)
    (fun _ => 5)) 5.
Ltac2 Eval
  match Control.case (fun () => Int.mul (two ()) 10) with
  | Val p =>
    let (v, k) := p in
    check_int v 10;
    match Control.case (fun () => k E1) with
    | Val p => let (v, _) := p in check_int v 20
    | Err _ => check false
    end
  | Err _ => check false
  end.

(** [Control.enter] builds the tactic of its body once and runs it in each goal: a closure called
    in the first step of the body runs once per goal, in goal order, and reads that goal. *)
Ltac2 goal_args () := match Constr.Unsafe.kind (Control.goal ()) with
                      | Constr.Unsafe.App _ args => Array.length args
                      | _ => 0
                      end.
Ltac2 args_plus (n : int) := Int.add (goal_args ()) n.
Goal True /\ 2 = 2.
Proof.
  split.
  all: let r := { c := 0 } in
  Control.enter (fun () => let n := args_plus 1 in r.(c) := Int.add (Int.mul (r.(c)) 10) n);
  check_int (r.(c)) 14.
  all: let r := { c := 0 } in
  Control.enter (fun () => match args_plus 0 with 0 => r.(c) := 7 | n => r.(c) := Int.add (r.(c)) n end);
  check_int (r.(c)) 10.
  all: check_int (Control.plus (fun () => Control.enter (fun () => let _ := fails_after { c := 0 } 6 in ()); 0)
                          (fun e => match e with E2 n => n | _ => 0 end)) 6.
  all: check_int (Control.numgoals ()) 2.
  Control.focus 1 1 (fun () => exact I).
  reflexivity.
Qed.

(** With backtraces or Ltac2-in-Ltac1 profiling on, the closure's frame must be pushed, so the
    general path runs; the values are the same. (The frames themselves are in
    output/ltac2_direct_prims_bt.v.) *)
Set Ltac2 Backtrace.
Ltac2 Eval check_int (in_arg ()) 9.
Ltac2 Eval check_int (lexical ()) 102.
Ltac2 Eval check_int (count_runs ()) 3.
Ltac2 Eval check_int (fact 10) 3628800.
Unset Ltac2 Backtrace.
Set Ltac2 In Ltac1 Profiling.
Ltac2 Eval check_int (in_arg ()) 9.
Ltac2 Eval check_int (partial ()) 15.
Ltac2 Eval check_int (local_rec ()) 1.
Unset Ltac2 In Ltac1 Profiling.
