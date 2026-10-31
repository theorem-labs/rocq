Require Import Ltac2.Ltac2.

(** The compiled body of an Ltac2 function ([Tac2interp], "Direct bodies") computes the value of a
    call without the proof monad until it meets a step that needs the monad: a primitive with an
    effect, a match or a call it cannot finish directly, or a nest of calls past a depth bound.
    There it stops, and the rest of the call (the arguments not yet computed, the call, the
    enclosing let, match, constructor, projection or write) runs as before, after that step. Each
    test below makes that step happen in one place of a body and checks the value, the order of
    the effects, and how many times each runs when the step succeeds twice (backtracking): the
    steps before it run once, the steps after it once per success. It also checks the steps that
    read the environment and the evar map ([Constr.Unsafe.kind], [Constr.equal]) before and after
    a step that changes the evar map; [Array.get], whose index is checked directly; partial
    applications and over-applications; nests of calls deeper than the bound; loops of tail calls
    through functions that are not compiled; and failures. *)

Ltac2 check (b : bool) := if b then () else Control.throw (Invalid_argument None).
Ltac2 check_int (n : int) (m : int) := check (Int.equal n m).
Ltac2 Type rr := { mutable c : int }.
Ltac2 log (r : rr) (d : int) := r.(c) := Int.add (Int.mul (r.(c)) 10) d.
Ltac2 logv (r : rr) (d : int) (v : int) := log r d; v.
Ltac2 Type exn ::= [ E1 | E2 (int) ].

(** [two ()] succeeds with 1, then with 2. [second f] is the second success of [f ()]. *)
Ltac2 two () := Control.plus (fun () => 1) (fun _ => 2).
Ltac2 second (f : unit -> 'a) : 'a :=
  let n := { c := 0 } in
  Control.once (fun () =>
    let v := f () in
    n.(c) := Int.add (n.(c)) 1;
    if Int.equal (n.(c)) 1 then Control.zero E1 else v).

(** In an argument, after a computed argument and before another, inside a nested call. *)
Ltac2 a_args (r : rr) := Int.add (logv r 1 1000) (Int.add (logv r 2 (two ())) (logv r 3 100)).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_args r)) 1102; check_int (r.(c)) 12323.

(** In the right-hand side of a let with several bindings, and of a sequence. *)
Ltac2 a_let (r : rr) := let x := logv r 1 10 with y := logv r 2 (two ()) with z := logv r 3 100 in Int.add x (Int.add y z).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_let r)) 112; check_int (r.(c)) 12323.
Ltac2 a_seq (r : rr) := let x := logv r 1 10 in let y := two () in log r 3; Int.add x y.
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_seq r)) 12; check_int (r.(c)) 133.

(** In the scrutinee of a match on a closed type, and of a full match on a tuple. *)
Ltac2 a_case (r : rr) := log r 9; match logv r 1 (two ()) with 1 => logv r 2 10 | _ => logv r 3 20 end.
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_case r)) 20; check_int (r.(c)) 91213.
Ltac2 a_full (r : rr) := log r 9; match (two (), logv r 1 0) with (1, _) => logv r 2 10 | (n, _) => logv r 3 n end.
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_full r)) 2; check_int (r.(c)) 91213.

(** In the scrutinee of a match on an open type. *)
Ltac2 a_open (r : rr) := log r 9; match E2 (logv r 1 (two ())) with E2 n => logv r 2 n | _ => logv r 3 0 end.
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_open r)) 2; check_int (r.(c)) 91212.

(** In a field of a record whose field is projected, in a called function. *)
Ltac2 Type rec3 := { fa : int; fb : int; fc : int }.
Ltac2 mk3 (r : rr) := { fa := logv r 1 0; fb := two (); fc := logv r 3 0 }.
Ltac2 a_proj (r : rr) := (mk3 r).(fb).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_proj r)) 2; check_int (r.(c)) 133.

(** In the value written to a field, and in the block written to. *)
Ltac2 a_set (r : rr) := let q := { c := 0 } in q.(c) := logv r 1 (two ()); log r 2; q.(c).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_set r)) 2; check_int (r.(c)) 1212.
Ltac2 a_set_target (r : rr) := let q := { c := 0 } in (let v := two () in log r v; q).(c) := logv r 9 5; q.(c).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_set_target r)) 5; check_int (r.(c)) 1929.

(** In the function of a call, which is computed. *)
Ltac2 a_head (r : rr) :=
  (if Int.equal (two ()) 1 then (fun x => logv r 2 x) else (fun x => logv r 3 (Int.add x 1))) (logv r 1 5).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_head r)) 6; check_int (r.(c)) 1213.

(** Deep inside a function called in an argument, and in a constructor argument of a list. *)
Ltac2 inner (r : rr) := Int.mul (logv r 2 1) (Int.add (two ()) (logv r 3 0)).
Ltac2 a_inner (r : rr) := Int.add (logv r 1 1) (inner r).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_inner r)) 3; check_int (r.(c)) 1233.
Ltac2 a_list (r : rr) := [logv r 1 0; inner r; logv r 4 0].
Ltac2 Eval let r := { c := 0 } in
  match second (fun () => a_list r) with
  | [_; v; _] => check_int v 2
  | _ => check false
  end;
  check_int (r.(c)) 123434.

(** The rest of a body runs directly again in the functions it calls after the step. *)
Ltac2 rec countdown (n : int) (acc : int) := if Int.equal n 0 then acc else countdown (Int.sub n 1) (Int.add acc n).
Ltac2 a_after (r : rr) := let t := two () in log r t; Int.add (countdown 100 0) t.
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => a_after r)) 5052; check_int (r.(c)) 12.

(** [Constr.Unsafe.kind] and [Constr.equal] read the evar map: an evar instantiated by a step of
    the body ([Std.unify]) is seen as its value by the steps after it, also in a function whose
    earlier calls read the evar map before the instantiation. *)
Ltac2 is_evar (c : constr) := match Constr.Unsafe.kind c with Constr.Unsafe.Evar _ _ => true | _ => false end.
Ltac2 eqz (c : constr) (z : constr) := Constr.equal c z.
Ltac2 kinds (r : rr) (c : constr) (z : constr) :=
  let b1 := is_evar c in
  let e1 := eqz c z in
  log r 1;
  let b2 := is_evar c in
  Std.unify c z;
  log r 2;
  let b3 := is_evar c in
  let e3 := eqz c z in
  [b1; e1; b2; b3; e3].
Ltac2 rec many_evar (n : int) (c : constr) := if Int.equal n 0 then true else Bool.and (is_evar c) (many_evar (Int.sub n 1) c).
(** A new evar of type [nat] (the ascription is a cast around it). *)
Ltac2 new_evar () :=
  match Constr.Unsafe.kind open_constr:(_ : nat) with Constr.Unsafe.Cast c _ _ => c | _ => Control.throw E1 end.
Ltac2 fkind (r : rr) (e : constr) :=
  match Constr.Unsafe.kind e with Constr.Unsafe.Evar _ _ => logv r 1 0 | _ => logv r 2 1 end.
Ltac2 kind_retry (r : rr) (e : constr) (z : constr) :=
  Int.add (fkind r e) (Int.add (Control.plus (fun () => Std.unify e z; 0) (fun _ => 10)) (fkind r e)).
Goal True.
  let r := { c := 0 } in
  let e := new_evar () in
  let z := '0 in
  check (many_evar 10 e);
  check (Bool.neg (eqz e z));
  match kinds r e z with
  | [b1; e1; b2; b3; e3] =>
    check b1; check (Bool.neg e1); check b2; check (Bool.neg b3); check e3
  | _ => check false
  end;
  check_int (r.(c)) 12;
  check (Bool.neg (many_evar 3 e));
  check (eqz e z).
  let e := new_evar () in
  let r := { c := 0 } in
  check_int (second (fun () => kind_retry r e '(S 0))) 10;
  check_int (r.(c)) 121.
Abort.

(** The state read before a step that changes the evar map is not used after it, at each place
    where the rest of a construct resumes after a step in the proof monad: a match, the function
    of a call, an argument, a constructor, the target and the value of a write, a full match, a
    match on an open type, and a let that starts after the state was read. *)
Ltac2 Type rb := { mutable bf : bool }.
Ltac2 st_case (c : constr) (z : constr) :=
  let b1 := is_evar c in match (Std.unify c z; 0) with 0 => [b1; is_evar c] | _ => [b1; true] end.
Ltac2 st_head (c : constr) (z : constr) :=
  let b1 := is_evar c in (Std.unify c z; fun x => [x; is_evar c]) b1.
Ltac2 st_arg (c : constr) (z : constr) :=
  let b1 := is_evar c in List.append [b1] ((fun _ => [is_evar c]) (Std.unify c z)).
Ltac2 st_ctor (c : constr) (z : constr) := let b1 := is_evar c in [b1; (Std.unify c z; false); is_evar c].
Ltac2 st_set (c : constr) (z : constr) :=
  let q := { bf := true } in let b1 := is_evar c in q.(bf) := (Std.unify c z; is_evar c); [b1; q.(bf)].
Ltac2 st_full (c : constr) (z : constr) :=
  let b1 := is_evar c in match ((Std.unify c z; 0), 1) with (0, _) => [b1; is_evar c] | _ => [b1; true] end.
Ltac2 st_open (c : constr) (z : constr) :=
  let b1 := is_evar c in match E2 (Std.unify c z; 0) with E2 _ => [b1; is_evar c] | _ => [b1; true] end.
Ltac2 st_case_opt (c : constr) (z : constr) :=
  let b1 := is_evar c in match (Std.unify c z; Some 0) with Some _ => [b1; is_evar c] | None => [b1; true] end.
Ltac2 st_set_target (c : constr) (z : constr) :=
  let q := { bf := true } in let b1 := is_evar c in (Std.unify c z; q).(bf) := is_evar c; [b1; q.(bf)].
Ltac2 st_let (c : constr) (z : constr) := let b1 := is_evar c in let _ := Std.unify c z in [b1; is_evar c].
Ltac2 st_let_in_branch (c : constr) (z : constr) :=
  match is_evar c with true => (let _ := Std.unify c z in [true; is_evar c]) | false => [false; true] end.
Ltac2 st_check (f : constr -> constr -> bool list) :=
  match f (new_evar ()) '0 with
  | [b1; b2] => check b1; check (Bool.neg b2)
  | [b1; _; b2] => check b1; check (Bool.neg b2)
  | _ => check false
  end.
Goal True.
  st_check st_case; st_check st_head; st_check st_arg; st_check st_ctor;
  st_check st_set; st_check st_full; st_check st_open;
  st_check st_case_opt; st_check st_set_target; st_check st_let; st_check st_let_in_branch.
Abort.

(** A loop of tail calls between a compiled function and a function that is not compiled (made
    by a let in a command), directly, after a step in the proof monad ([Constr.equal] reads the
    evar map) and through an over-application, and a deep nest of such calls not in tail
    position. *)
Ltac2 app (f : int -> int) (x : int) := f x.
Ltac2 Eval check_int (let rec go n := if Int.equal n 0 then 0 else app go (Int.sub n 1) in go 1000000) 0.
Ltac2 Eval check_int (let rec go n := if Int.equal n 0 then 0 else Int.add 1 (app go (Int.sub n 1)) in go 100000) 100000.
Ltac2 app_env (c : constr) (f : int -> int) (x : int) := let _ := Constr.equal c c in f x.
Ltac2 over2 (h : unit -> int -> int) (n : int) := h () n.
Ltac2 Eval check_int (let rec h _ := fun m => if Int.equal m 0 then 0 else over2 h (Int.sub m 1) in over2 h 1000000) 0.
Ltac2 Eval check_int (let rec f n := match (n, 0) with (0, _) => 0 | (m, _) => f (Int.sub m 1) end in f 1000000) 0.
Ltac2 Eval check_int (let c := 'True in let rec go n := if Int.equal n 0 then 0 else app_env c go (Int.sub n 1) in go 1000000) 0.

(** [Array.get]: in bounds, out of bounds (the primitive's error, which [Control.throw] raises
    and no handler catches), partially applied, and in [Array.fold_left], which calls it at each
    index. *)
Ltac2 gets () :=
  let a := Array.of_list [10; 20; 30] in
  [Array.get a 0; Array.get a 2; Array.fold_left Int.add 0 a;
   List.fold_left Int.add 0 (List.map (Array.get a) [2; 0])].
Ltac2 Eval
  match gets () with
  | [a; b; c; d] => check_int a 10; check_int b 30; check_int c 60; check_int d 40
  | _ => check false
  end.
Ltac2 get_at (r : rr) (i : int) := let a := Array.of_list [1; 2; 3] in Int.add (logv r 1 0) (Array.get a i).
Ltac2 Eval let r := { c := 0 } in check_int (get_at r 2) 3; check_int (r.(c)) 1.
Fail Ltac2 Eval get_at { c := 0 } 3.
Fail Ltac2 Eval get_at { c := 0 } -1.
Ltac2 get_partial_oob () := let a := Array.of_list [1; 2] in List.map (Array.get a) [0; 5].
Fail Ltac2 Eval get_partial_oob ().
Ltac2 get_write () :=
  let a := Array.make 3 0 in
  Array.set a 1 7; let x := Array.get a 1 in Array.set a 1 8; Int.add (Int.mul x 10) (Array.get a 1).
Ltac2 Eval check_int (get_write ()) 78.

(** Partial applications: of a function that reads the evar map, of a partial application, with
    no effect until the last argument; over-application of a function that returns a function. *)
Ltac2 sub3 (a : int) (b : int) (c : int) := Int.sub a (Int.sub b c).
Ltac2 logsub (r : rr) (a : int) (b : int) := log r a; log r b; Int.sub a b.
Ltac2 partials (r : rr) :=
  let f := logsub r 9 in
  log r 1;
  let g := sub3 100 in
  let h := g 10 in
  let l := List.map f [3; 2] in
  [h 1; List.fold_left Int.add 0 l; (fun a => fun b => Int.sub a b) 10 3;
   List.length (List.filter (Constr.equal '0) ['0; '1; '0])].
Ltac2 Eval let r := { c := 0 } in
  match partials r with
  | [a; b; c; d] => check_int a 91; check_int b 13; check_int c 7; check_int d 2
  | _ => check false
  end;
  check_int (r.(c)) 19392.

(** Nests of calls deeper than the bound: non-tail recursion, with an effect at each level and a
    step at the bottom that succeeds twice; a map over a long list. *)
Ltac2 rec sumto (n : int) := if Int.equal n 0 then 0 else Int.add n (sumto (Int.sub n 1)).
Ltac2 Eval check_int (sumto 20000) 200010000.
Ltac2 bump (r : rr) := r.(c) := Int.add (r.(c)) 1.
Ltac2 rec deep_two (r : rr) (n : int) :=
  if Int.equal n 0 then two () else (bump r; Int.add 0 (deep_two r (Int.sub n 1))).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => deep_two r 3000)) 2; check_int (r.(c)) 3000.
Ltac2 sum_succ (n : int) := List.fold_left Int.add 0 (List.map (fun x => Int.add x 1) (List.seq 0 1 n)).
Ltac2 Eval check_int (sum_succ 5000) 12502500.

(** Failures: an exception raised inside nested calls, after some steps and before others. *)
Ltac2 thrower (r : rr) := Int.add (logv r 1 0) (Int.add (Control.zero (E2 (logv r 2 5))) (logv r 3 0)).
Ltac2 panic (r : rr) := Int.add (logv r 1 0) (Int.add (Control.throw (E2 (logv r 2 5))) (logv r 3 0)).
Fail Ltac2 Eval panic { c := 0 }.
Ltac2 Eval let r := { c := 0 } in
  check_int (match Control.case (fun () => thrower r) with Val _ => 0 | Err e => match e with E2 n => n | _ => -1 end end) 5;
  check_int (r.(c)) 12.
Ltac2 inner_zero (r : rr) := Int.mul (logv r 2 1) (Control.zero (E2 (logv r 3 7))).
Ltac2 zero_deep (r : rr) := Int.add (logv r 1 0) (Int.add (inner_zero r) (logv r 4 0)).
Ltac2 Eval let r := { c := 0 } in
  check_int (Control.plus (fun () => zero_deep r) (fun e => match e with E2 n => n | _ => -1 end)) 7;
  check_int (r.(c)) 123.
