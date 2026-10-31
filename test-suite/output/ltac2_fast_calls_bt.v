Require Import Ltac2.Ltac2.

(** Backtrace frames of calls of one to five arguments that pass their arguments without a list
    ([Tac2val.fast]), of the call of a partial application, and of [Array.get] out of bounds:
    once [Set Ltac2 Backtrace] is on, the frame of each call appears, down to the one that
    fails, as on the general path. *)

Ltac2 Type exn ::= [ E ].
Ltac2 fail1 (x : int) := if Int.equal x 0 then Control.throw E else x.
Ltac2 g2 (a : int) (b : int) := Int.add a (fail1 b).
Ltac2 g3 (a : int) (b : int) (c : int) := g2 a (Int.add b c).
Ltac2 g4 (a : int) (b : int) (c : int) (d : int) := g3 a b (Int.sub c d).
Ltac2 g5 (a : int) (b : int) (c : int) (d : int) (e : int) := let p := g4 a b in p c (Int.add d e).
Ltac2 aget (a : int array) (i : int) := Array.get a i.

(** With backtraces off, the same calls run. *)
Ltac2 Eval g5 1 2 3 4 5.
Fail Ltac2 Eval g5 1 0 0 0 0.

Set Ltac2 Backtrace.
Fail Ltac2 Eval g5 1 0 0 0 0.
Fail Ltac2 Eval aget (Array.make 2 0) 5.
Unset Ltac2 Backtrace.
Fail Ltac2 Eval g5 1 0 0 0 0.
