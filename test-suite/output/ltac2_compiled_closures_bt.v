Require Import Ltac2.Ltac2.

(** Backtrace frames of Ltac2 functions whose bodies run as compiled code while backtraces are off:
    once [Set Ltac2 Backtrace] is on, the frames appear for a partial application applied by
    another function, for a local recursive function, and under a constructor, a record field and
    a match on an open type. *)

Ltac2 Type exn ::= [ E | F (int) ].
Ltac2 fail_at (x : int) (y : int) : int := match Int.equal x y with true => 0 | false => Control.throw E end.
Ltac2 map_partial (n : int) := List.map (fail_at n) [n; 1].
Ltac2 local_rec (n : int) :=
  let rec go i := if Int.equal i 0 then fail_at n 1 else Int.add 1 (go (Int.sub i 1)) in go 2.
Ltac2 in_ctor (n : int) := (1, Some (fail_at n 1)).
Ltac2 of_open (e : exn) := match e with F n => fail_at n 1 | _ => 0 end.

(** With backtraces off, the same calls run. *)
Ltac2 Eval map_partial 1.
Ltac2 Eval local_rec 1.
Ltac2 Eval in_ctor 1.
Ltac2 Eval of_open (F 1).
Fail Ltac2 Eval map_partial 2.

Set Ltac2 Backtrace.
Fail Ltac2 Eval map_partial 2.
Fail Ltac2 Eval local_rec 2.
Fail Ltac2 Eval in_ctor 2.
Fail Ltac2 Eval of_open (F 2).
Unset Ltac2 Backtrace.
Fail Ltac2 Eval local_rec 2.
