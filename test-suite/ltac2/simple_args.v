From Ltac2 Require Import Ltac2.
From Ltac2 Require List.

(** An application whose arguments are all simple (atoms, variables, globals, functions, primitives,
    and constructors, open constructors and projections of such), with at most 64 nodes in all, has
    its arguments evaluated in one step; any other takes the monadic path. Both must give the values
    stock's monadic path gives. *)

Ltac2 assert_int a b := Control.assert_true (Int.equal a b).

(** A string literal is a new mutable string each time it is evaluated. *)
Ltac2 id_str (s : string) := s.
Ltac2 first_then_set () :=
  let s := id_str "aaa" in
  let c := Char.to_int (String.get s 0) in
  String.set s 0 (Char.of_int 98); c.
Ltac2 Eval assert_int (first_then_set ()) 97.
Ltac2 Eval assert_int (first_then_set ()) 97.

(** A record with a mutable field is a new block each time the continuation that builds it runs,
    also when backtracking runs it again. *)
Ltac2 Type rr := { mutable v : int }.
Ltac2 id_rr (r : rr) := r.
Ltac2 Eval
  let n := Control.plus (fun () => 1) (fun _ => 2) in
  let r := id_rr { v := 0 } in
  r.(v) := Int.add (r.(v)) n;
  match Int.equal n 1 with
  | true => Control.zero Not_found
  | false => ()
  end;
  assert_int (r.(v)) 2.

(** Projections, closures and tuples as arguments. *)
Ltac2 id_int (n : int) := n.
Ltac2 Eval let r := { v := 5 } in assert_int (id_int (r.(v))) 5.
Ltac2 Eval assert_int (List.nth (List.map (fun x => Int.add x 1) [1; 2; 3]) 2) 4.
Ltac2 fst3 (p : int * int * int) := match p with (a, _, _) => a end.
Ltac2 Eval assert_int (fst3 (7, 8, 9)) 7.

(** Either side of the 64-node budget: n list elements are 2n+1 nodes. *)
Ltac2 Eval
  let l := List.rev [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31] in
  assert_int (List.length l) 31; assert_int (List.nth l 0) 31; assert_int (List.nth l 30) 1.
Ltac2 Eval
  let l := List.rev [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32] in
  assert_int (List.length l) 32; assert_int (List.nth l 0) 32; assert_int (List.nth l 31) 1.
Ltac2 Eval
  let l := List.rev [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100] in
  assert_int (List.length l) 100; assert_int (List.nth l 0) 100; assert_int (List.nth l 99) 1.
