(* The interpreter keeps the newest bindings of an environment in a chain of at most 16 and the
   older ones in a map under it. These tests read names on both sides of that boundary, across
   shadowing, through captured closures and through recursion, and check every value. *)

Require Import Ltac2.Ltac2.

(* The shadowed bindings are unused on purpose. *)
Set Warnings "-ltac2-unused-variable".

Ltac2 check (b : bool) := Control.assert_true b.

(* Forty distinct names in one body: the oldest move into the map. *)
Ltac2 distinct () :=
  let x1 := 1 in let x2 := 2 in let x3 := 3 in let x4 := 4 in let x5 := 5 in
  let x6 := 6 in let x7 := 7 in let x8 := 8 in let x9 := 9 in let x10 := 10 in
  let x11 := 11 in let x12 := 12 in let x13 := 13 in let x14 := 14 in let x15 := 15 in
  let x16 := 16 in let x17 := 17 in let x18 := 18 in let x19 := 19 in let x20 := 20 in
  let x21 := 21 in let x22 := 22 in let x23 := 23 in let x24 := 24 in let x25 := 25 in
  let x26 := 26 in let x27 := 27 in let x28 := 28 in let x29 := 29 in let x30 := 30 in
  let x31 := 31 in let x32 := 32 in let x33 := 33 in let x34 := 34 in let x35 := 35 in
  let x36 := 36 in let x37 := 37 in let x38 := 38 in let x39 := 39 in let x40 := 40 in
  check (Int.equal x1 1);
  check (Int.equal x16 16);
  check (Int.equal x17 17);
  check (Int.equal x18 18);
  check (Int.equal x40 40);
  let _ := (x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15) in
  let _ := (x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30) in
  let _ := (x31, x32, x33, x34, x35, x36, x37, x38, x39) in
  ().

Ltac2 Eval distinct ().

(* One name shadowed forty times with distinct values; closures captured after the 10th, 16th and
   17th binding read the value they captured. Twenty more names then push every [x] into the map,
   where the newest must still win. *)
Ltac2 shadow () :=
  let x := 1 in let x := 2 in let x := 3 in let x := 4 in let x := 5 in
  let x := 6 in let x := 7 in let x := 8 in let x := 9 in let x := 10 in
  let c10 := fun () => x in
  let x := 11 in let x := 12 in let x := 13 in let x := 14 in let x := 15 in
  let x := 16 in
  let c16 := fun () => x in
  let x := 17 in
  let c17 := fun () => x in
  let x := 18 in let x := 19 in let x := 20 in
  let x := 21 in let x := 22 in let x := 23 in let x := 24 in let x := 25 in
  let x := 26 in let x := 27 in let x := 28 in let x := 29 in let x := 30 in
  let x := 31 in let x := 32 in let x := 33 in let x := 34 in let x := 35 in
  let x := 36 in let x := 37 in let x := 38 in let x := 39 in let x := 40 in
  check (Int.equal x 40);
  check (Int.equal (c10 ()) 10);
  check (Int.equal (c16 ()) 16);
  check (Int.equal (c17 ()) 17);
  let y1 := 1 in let y2 := 2 in let y3 := 3 in let y4 := 4 in let y5 := 5 in
  let y6 := 6 in let y7 := 7 in let y8 := 8 in let y9 := 9 in let y10 := 10 in
  let y11 := 11 in let y12 := 12 in let y13 := 13 in let y14 := 14 in let y15 := 15 in
  let y16 := 16 in let y17 := 17 in let y18 := 18 in let y19 := 19 in let y20 := 20 in
  check (Int.equal x 40);
  check (Int.equal (c10 ()) 10);
  check (Int.equal (c16 ()) 16);
  check (Int.equal (c17 ()) 17);
  let _ := (y1, y2, y3, y4, y5, y6, y7, y8, y9, y10) in
  let _ := (y11, y12, y13, y14, y15, y16, y17, y18, y19, y20) in
  ().

Ltac2 Eval shadow ().

(* A name bound under thirty shadows of another one. *)
Ltac2 under () :=
  let y := 7 in
  let x := 0 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  let x := Int.add x 1 in let x := Int.add x 1 in let x := Int.add x 1 in
  check (Int.equal y 7);
  check (Int.equal x 30).

Ltac2 Eval under ().

(* A recursive function defined under fifteen names, so its closure environment fills the chain and
   every call overflows it. Each level binds a local and checks it, the argument and an outer name
   after the deeper levels return. *)
Ltac2 recursive () :=
  let p1 := 1 in let p2 := 2 in let p3 := 3 in let p4 := 4 in let p5 := 5 in
  let p6 := 6 in let p7 := 7 in let p8 := 8 in let p9 := 9 in let p10 := 10 in
  let p11 := 11 in let p12 := 12 in let p13 := 13 in let p14 := 14 in let p15 := 15 in
  let rec go n :=
    if Int.equal n 0 then 0 else
    let l := Int.mul n 100 in
    let below := go (Int.sub n 1) in
    check (Int.equal l (Int.mul n 100));
    check (Int.equal p1 1);
    check (Int.equal p15 15);
    check (Int.equal below (Int.sub n 1));
    n
  in
  check (Int.equal (go 40) 40);
  let _ := (p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14) in
  ().

Ltac2 Eval recursive ().
