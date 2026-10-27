Require Import Ltac2.Ltac2.

(** Compiled Ltac2 code calls a function of one to five arguments without building the list of
    its arguments ([Tac2interp], "Calls of one to five arguments"; [Tac2val.fast]): an Ltac2
    function, the function a partial application gives, and a primitive whose result is pure or
    reads the evar map, or whose value is checked ([Array.get]). Each test below gives the value
    and the order of the effects that the general path gives, for each number of arguments, with
    a step in the proof monad in each argument position (run once before it, once per success
    after it), for partial applications at each number of given arguments, for arguments bound to
    [_], for over-applications, for primitives before and after a step that changes the evar map,
    and for a long loop of tail calls through a function of five arguments. *)

Ltac2 check (b : bool) := if b then () else Control.throw (Invalid_argument None).
Ltac2 check_int (n : int) (m : int) := check (Int.equal n m).
Ltac2 Type rr := { mutable c : int }.
Ltac2 log (r : rr) (d : int) := r.(c) := Int.add (Int.mul (r.(c)) 10) d.
Ltac2 logv (r : rr) (d : int) (v : int) := log r d; v.
Ltac2 Type exn ::= [ E1 ].

(** [two ()] succeeds with 1, then with 2. [second f] is the second success of [f ()]. *)
Ltac2 two () := Control.plus (fun () => 1) (fun _ => 2).
Ltac2 second (f : unit -> 'a) : 'a :=
  let n := { c := 0 } in
  Control.once (fun () =>
    let v := f () in
    n.(c) := Int.add (n.(c)) 1;
    if Int.equal (n.(c)) 1 then Control.zero E1 else v).

(** Functions of one to five arguments, each argument with its own weight. *)
Ltac2 f1 (a : int) := Int.mul a 3.
Ltac2 f2 (a : int) (b : int) := Int.add (Int.mul a 10) b.
Ltac2 f3 (a : int) (b : int) (c : int) := Int.add (Int.mul (f2 a b) 10) c.
Ltac2 f4 (a : int) (b : int) (c : int) (d : int) := Int.add (Int.mul (f3 a b c) 10) d.
Ltac2 f5 (a : int) (b : int) (c : int) (d : int) (e : int) := Int.add (Int.mul (f4 a b c d) 10) e.

(** Simple arguments, and arguments that are calls. *)
Ltac2 s_all () := [f1 7; f2 1 2; f3 1 2 3; f4 1 2 3 4; f5 1 2 3 4 5].
Ltac2 Eval match s_all () with
  | [a; b; c; d; e] => check_int a 21; check_int b 12; check_int c 123; check_int d 1234; check_int e 12345
  | _ => check false
  end.
Ltac2 c_all () :=
  [f1 (f1 1); f2 (f1 1) (f1 2); f3 (f1 1) 2 (f1 1); f4 1 (f1 1) 3 (f1 1); f5 (f1 1) 2 (f1 1) 4 (f1 3)].
Ltac2 Eval match c_all () with
  | [a; b; c; d; e] => check_int a 9; check_int b 36; check_int c 323; check_int d 1333; check_int e 32349
  | _ => check false
  end.

(** The function of the call computed (not simple), with simple arguments and with calls as
    arguments. *)
Ltac2 pick (b : bool) := if b then f5 else (fun a b c d e => f5 e d c b a).
Ltac2 computed () :=
  [(pick true) 1 2 3 4 5; (pick false) 1 2 3 4 5; (pick false) (f1 1) 2 3 4 (f1 2);
   (if true then f1 else f1) 4; (if true then f2 else f2) 1 2; (if true then f3 else f3) 1 2 3;
   (if true then f4 else f4) 1 2 3 4; (if true then f4 else f4) 1 (f1 1) 3 (f1 2)].
Ltac2 Eval check (List.equal Int.equal (computed ()) [12345; 54321; 64323; 12; 12; 123; 1234; 1336]).

(** Arguments run from left to right, each once. *)
Ltac2 order5 (r : rr) := f5 (logv r 1 1) (logv r 2 2) (logv r 3 3) (logv r 4 4) (logv r 5 5).
Ltac2 Eval let r := { c := 0 } in check_int (order5 r) 12345; check_int (r.(c)) 12345.

(** A step in the proof monad in each argument position: the arguments before it run once, the
    ones after it once per success of the step. *)
Ltac2 m1 (r : rr) := f1 (logv r 1 (two ())).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m1 r)) 6; check_int (r.(c)) 11.
Ltac2 m2a (r : rr) := f2 (two ()) (logv r 2 5).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m2a r)) 25; check_int (r.(c)) 22.
Ltac2 m2b (r : rr) := f2 (logv r 1 5) (two ()).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m2b r)) 52; check_int (r.(c)) 1.
Ltac2 m3a (r : rr) := f3 (logv r 1 1) (two ()) (logv r 3 3).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m3a r)) 123; check_int (r.(c)) 133.
Ltac2 m3b (r : rr) := f3 (logv r 1 1) (logv r 2 2) (two ()).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m3b r)) 122; check_int (r.(c)) 12.
Ltac2 m4a (r : rr) := f4 (two ()) (logv r 2 2) (logv r 3 3) (logv r 4 4).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m4a r)) 2234; check_int (r.(c)) 234234.
Ltac2 m4b (r : rr) := f4 (logv r 1 1) (logv r 2 2) (two ()) (logv r 4 4).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m4b r)) 1224; check_int (r.(c)) 1244.
Ltac2 m4c (r : rr) := f4 (logv r 1 1) (logv r 2 2) (logv r 3 3) (two ()).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m4c r)) 1232; check_int (r.(c)) 123.
Ltac2 m5a (r : rr) := f5 (logv r 1 1) (two ()) (logv r 3 3) (logv r 4 4) (logv r 5 5).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m5a r)) 12345; check_int (r.(c)) 1345345.
Ltac2 m5b (r : rr) := f5 (logv r 1 1) (logv r 2 2) (logv r 3 3) (two ()) (logv r 5 5).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m5b r)) 12325; check_int (r.(c)) 12355.
Ltac2 m5c (r : rr) := f5 (logv r 1 1) (logv r 2 2) (logv r 3 3) (logv r 4 4) (two ()).
Ltac2 Eval let r := { c := 0 } in check_int (second (fun () => m5c r)) 12342; check_int (r.(c)) 1234.

(** Partial applications at each number of given arguments, called once and twice. *)
Ltac2 partials () :=
  let p21 := f2 1 in
  let p31 := f3 1 in let p32 := f3 1 2 in
  let p41 := f4 1 in let p42 := f4 1 2 in let p43 := f4 1 2 3 in
  let p51 := f5 1 in let p52 := f5 1 2 in let p53 := f5 1 2 3 in let p54 := f5 1 2 3 4 in
  [p21 2; p21 3; p31 2 3; p32 3; p32 4; p41 2 3 4; p42 3 4; p43 4; p43 5;
   p51 2 3 4 5; p52 3 4 5; p53 4 5; p54 5; p54 6].
Ltac2 Eval check (List.equal Int.equal (partials ())
  [12; 13; 123; 123; 124; 1234; 1234; 1234; 1235; 12345; 12345; 12345; 12345; 12346]).
(** A partial application of a partial application. *)
Ltac2 partial2 () := let p := f5 1 in let q := p 2 3 in let s := q 4 in [s 5; q 4 6; p 2 3 4 7].
Ltac2 Eval check (List.equal Int.equal (partial2 ()) [12345; 12346; 12347]).
(** A partial application whose body has an effect: it runs at each full call only. *)
Ltac2 eff3 (r : rr) (a : int) (b : int) := log r a; logv r b (Int.add a b).
Ltac2 partial_eff (r : rr) := let p := eff3 r 1 in log r 9; let x := p 2 in let y := p 3 in Int.add x y.
Ltac2 Eval let r := { c := 0 } in check_int (partial_eff r) 7; check_int (r.(c)) 91213.

(** Arguments bound to [_]. *)
Ltac2 k5 (_ : int) (b : int) (_ : int) (d : int) (_ : int) := f2 b d.
Ltac2 k2 (_ : int) (b : int) := b.
Ltac2 Eval check_int (k5 1 2 3 4 5) 24; check_int (k2 1 2) 2; check_int (let p := k5 9 8 in p 7 6 5) 86.

(** Over-application: a function of two arguments that returns a function. *)
Ltac2 adder (a : int) (b : int) := fun c => f3 a b c.
Ltac2 Eval check_int (adder 1 2 3) 123; check_int (let p := adder 1 in p 2 4) 124.

(** Local functions, made by [fun] in a compiled body and by a recursive let. *)
Ltac2 locals (x : int) :=
  let g := fun a b c => f3 a b (Int.add c x) in
  let rec h a b c d e := if Int.equal a 0 then f5 a b c d e else h (Int.sub a 1) b c d e in
  [g 1 2 3; h 3 1 2 3 4; (g 4) 5 6].
Ltac2 Eval check (List.equal Int.equal (locals 1) [124; 1234; 457]).

(** Pure primitives of one to three arguments, given all their arguments and fewer. *)
Ltac2 prims () :=
  let m := FMap.add 1 10 (FMap.add 2 20 (FMap.empty FSet.Tags.int_tag)) in
  let add1 := FMap.add 3 in
  let m := add1 30 m in
  let add2 := FMap.add 4 40 in
  let m := add2 m in
  [Int.neg 5; Int.add 2 3; Int.sub 2 3; (Int.add 4) 5;
   match FMap.find_opt 1 m with Some v => v | None => 0 end;
   match FMap.find_opt 3 m with Some v => v | None => 0 end;
   match FMap.find_opt 4 m with Some v => v | None => 0 end;
   FMap.cardinal m].
Ltac2 Eval check (List.equal Int.equal (prims ()) [-5; 5; -1; 9; 10; 30; 40; 4]).

(** [Array.get] in bounds, out of bounds (the primitive's error, which [Control.case] does not
    catch), and given one argument. *)
Ltac2 aget (a : int array) (i : int) := Array.get a i.
Ltac2 Eval
  let a := Array.make 3 7 in
  Array.set a 1 8;
  check_int (aget a 1) 8;
  check_int ((Array.get a) 2) 7.
Fail Ltac2 Eval let a := Array.make 3 7 in aget a 3.

(** [Constr.Unsafe.kind] (one argument) and [Constr.equal] (two, and one given), at the start of
    a function, where the evar map is not known yet, and after a step that instantiates an evar. *)
Ltac2 is_evar (c : constr) := match Constr.Unsafe.kind c with Constr.Unsafe.Evar _ _ => true | _ => false end.
Ltac2 new_evar () :=
  match Constr.Unsafe.kind open_constr:(_ : nat) with Constr.Unsafe.Cast c _ _ => c | _ => Control.throw E1 end.
Ltac2 env_prims (c : constr) (z : constr) :=
  let b1 := is_evar c in
  let e1 := Constr.equal c z in
  let eq_c := Constr.equal c in
  let e2 := eq_c z in
  Std.unify c z;
  let b3 := is_evar c in
  let e3 := Constr.equal c z in
  let e4 := eq_c z in
  [b1; e1; e2; b3; e3; e4].
Goal True.
  let e := new_evar () in
  check (List.equal Bool.equal (env_prims e '0) [true; false; false; false; true; true]).
Abort.

(** A long loop of tail calls through a function of five arguments, and through the partial
    application of one, runs in constant stack. *)
Ltac2 rec loop5 (n : int) (a : int) (b : int) (c : int) (d : int) :=
  if Int.equal n 0 then Int.add a (Int.add b (Int.add c d)) else loop5 (Int.sub n 1) b c d (Int.add a 1).
Ltac2 Eval check_int (loop5 200000 0 0 0 0) 200000.
Ltac2 rec ploop (n : int) (acc : int) (_ : int) := if Int.equal n 0 then acc else (ploop (Int.sub n 1)) (Int.add acc 1) 0.
Ltac2 Eval check_int (ploop 200000 0 0) 200000.
(** [Array.fold_left] with a partial application of a function of four arguments, the shape of
    the loop that motivated this ([Array.fold_left (scan k nk) acc args]). *)
Ltac2 scan4 (k : int) (m : int) (acc : int) (x : int) := Int.add acc (Int.add (Int.mul k x) m).
Ltac2 Eval check_int (Array.fold_left (scan4 2 1) 0 (Array.make 1000 3)) 7000.
