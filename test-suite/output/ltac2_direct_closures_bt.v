Require Import Ltac2.Ltac2.

(** Backtrace frames of Ltac2 functions that already ran with backtraces off: the interpreter runs
    the body of a closure directly only while applying it pushes no frame, and it reads the flag
    each time the closure is applied, not when the closure was made (the values of global
    functions are made once and kept). So once [Set Ltac2 Backtrace] is on, the frames of [g],
    [fail_in] and [h] appear, in every position of the call: the tail of a function, the
    right-hand side of a let, a match scrutinee and an argument. *)

Ltac2 Type exn ::= [ E ].
Ltac2 fail_in (x : int) : int := match Int.equal x 100 with true => 0 | false => Control.throw E end.
Ltac2 g (x : int) := let y := fail_in x in Int.add y 1.
Ltac2 h (x : int) := match g x with 0 => 0 | n => Int.add n (g (Int.add x 0)) end.
Ltac2 tail (x : int) := g x.

(** With backtraces off, the same calls run (and are kept by the cache of global values). *)
Ltac2 Eval h 100.
Ltac2 Eval tail 100.
Fail Ltac2 Eval h 1.

Set Ltac2 Backtrace.
Fail Ltac2 Eval h 1.
Fail Ltac2 Eval tail 1.
Fail Ltac2 Eval Int.add 1 (g 2).
Unset Ltac2 Backtrace.
Fail Ltac2 Eval tail 1.
