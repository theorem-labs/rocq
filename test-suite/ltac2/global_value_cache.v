(* The interpreter computes the value of a global reference at each use (Tac2interp.eval_global),
   so each use of a global whose value holds a block gets its own block: mutating the value of one
   use never changes what the next use reads.

   Every test below mutates the value of one use of a global and then reads that global again. Each
   must see the unmutated value. They fail on an interpreter that reuses one value for a global
   whose value holds a block, a closure that captured one, a projection of one, a field of a record
   or the argument of an open constructor.

   The mutation goes through array_set, the primitive behind Ltac2.Array.set. Its implementation
   accepts any block (plugins/ltac2/tac2core.ml, "array_set", and Tac2ffi.to_block), so an external
   declared at a permissive type reaches the fields of a tuple, of a record and of an exception
   argument. Declaring it is what a user can do: a primitive's declared Ltac2 type is not checked
   against its implementation (plugins/ltac2/tac2entries.ml, register_primitive). *)

Require Import Ltac2.Ltac2.

Ltac2 @ external raw_set : 'a -> int -> 'b -> unit :=
  "rocq-runtime.plugins.ltac2" "array_set".

Ltac2 check_fst_is_zero (p : int * int) := Control.assert_true (Int.equal (fst p) 0).

(* A tuple. *)
Ltac2 global_pair := (0, 0).

Ltac2 Eval
  raw_set global_pair 0 1;
  check_fst_is_zero global_pair.

(* A global that is another global's value. *)
Ltac2 alias_pair := global_pair.

Ltac2 Eval
  raw_set alias_pair 0 1;
  check_fst_is_zero alias_pair.

(* A closure that captured a tuple: the tuple is the one its own evaluation built. *)
Ltac2 captured_pair := let p := (0, 0) in fun () => p.

Ltac2 Eval
  raw_set (captured_pair ()) 0 1;
  check_fst_is_zero (captured_pair ()).

(* The same through a recursive closure. *)
Ltac2 recursive_captured_pair :=
  let p := (0, 0) in
  let rec go (n : int) := if Int.equal n 0 then p else go (Int.sub n 1) in
  go.

Ltac2 Eval
  raw_set (recursive_captured_pair 2) 0 1;
  check_fst_is_zero (recursive_captured_pair 2).

(* A record of immutable fields is a syntactic value, and its fields are blocks. *)
Ltac2 Type boxed_pair := { boxed : int * int }.

Ltac2 global_record := { boxed := (0, 0) }.

Ltac2 Eval
  raw_set (global_record.(boxed)) 0 1;
  check_fst_is_zero (global_record.(boxed)).

(* A projection of a record global. *)
Ltac2 projected_pair := global_record.(boxed).

Ltac2 Eval
  raw_set projected_pair 0 1;
  check_fst_is_zero projected_pair.

(* The argument of an open constructor. *)
Ltac2 Type exn ::= [ PairExn (int * int) ].

Ltac2 global_exn := PairExn (0, 0).

Ltac2 pair_of_exn (e : exn) := match e with PairExn p => p | _ => (9, 9) end.

Ltac2 Eval
  raw_set (pair_of_exn global_exn) 0 1;
  check_fst_is_zero (pair_of_exn global_exn).

(* A closure that builds its tuple when it is called shares nothing between calls. *)
Ltac2 fresh_pair () := (0, 0).

Ltac2 Eval
  raw_set (fresh_pair ()) 0 1;
  check_fst_is_zero (fresh_pair ()).
