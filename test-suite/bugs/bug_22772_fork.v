(* Fork probe for rocq#22772 (upstream fix in rocq-prover/rocq#22776).  The
   lazy machine dropped the shift on a primitive array found under a binder,
   so [lazy] and [cbv] disagreed.  Every pair below must have the same normal
   form, compared syntactically. *)

From Corelib Require Import PrimInt63 PrimArray PrimFloat.

Open Scope array_scope.

Ltac check_const_eq name constr :=
  let v := (eval cbv delta [name] in name) in
  tryif constr_eq v constr
  then idtac
  else fail 0 v "<>" constr.

Notation check_const_eq name constr := (ltac:(check_const_eq name constr; exact constr)) (only parsing).

(* 1. the term of the issue *)
Definition lazy1 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => get a 0) [| x | x |].
Definition cbv1 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => get a 0) [| x | x |].
Check check_const_eq lazy1 (fun x _ : bool => x).
Check check_const_eq cbv1 (fun x _ : bool => x).

(* 2. nested binders *)
Definition lazy2 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y z w : bool) => get a 0) [| x | x |].
Definition cbv2 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y z w : bool) => get a 0) [| x | x |].
Check check_const_eq lazy2 (fun x _ _ _ : bool => x).
Check check_const_eq cbv2 (fun x _ _ _ : bool => x).

(* 3. two arrays *)
Definition lazy3 := Eval lazy in
  fun x x' : bool =>
    (fun (a b : array bool) (y : bool) => (get a 0, get b 1))
      [| x | x |] [| x ; x' | x |].
Definition cbv3 := Eval cbv in
  fun x x' : bool =>
    (fun (a b : array bool) (y : bool) => (get a 0, get b 1))
      [| x | x |] [| x ; x' | x |].
Check check_const_eq lazy3 (fun x x' _ : bool => (x, x')).
Check check_const_eq cbv3 (fun x x' _ : bool => (x, x')).

(* 4. set *)
Definition lazy4 := Eval lazy in
  fun x x' : bool => (fun (a : array bool) (y : bool) => get (set a 0 x') 0) [| x | x |].
Definition cbv4 := Eval cbv in
  fun x x' : bool => (fun (a : array bool) (y : bool) => get (set a 0 x') 0) [| x | x |].
Check check_const_eq lazy4 (fun _ x' _ : bool => x').
Check check_const_eq cbv4 (fun _ x' _ : bool => x').

(* 5. copy *)
Definition lazy5 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => get (copy a) 0) [| x | x |].
Definition cbv5 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => get (copy a) 0) [| x | x |].
Check check_const_eq lazy5 (fun x _ : bool => x).
Check check_const_eq cbv5 (fun x _ : bool => x).

(* 6. default *)
Definition lazy6 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => default a) [| x | x |].
Definition cbv6 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => default a) [| x | x |].
Check check_const_eq lazy6 (fun x _ : bool => x).
Check check_const_eq cbv6 (fun x _ : bool => x).

(* 7. out-of-bounds get *)
Definition lazy7 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => get a 17) [| x | x |].
Definition cbv7 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => get a 17) [| x | x |].
Check check_const_eq lazy7 (fun x _ : bool => x).
Check check_const_eq cbv7 (fun x _ : bool => x).

(* 8. array read as the scrutinee of an if *)
Definition lazy8 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => if get a 0 then y else y) [| x | x |].
Definition cbv8 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => if get a 0 then y else y) [| x | x |].
Check check_const_eq lazy8 (fun x y : bool => if x then y else y).
Check check_const_eq cbv8 (fun x y : bool => if x then y else y).

(* 9. array read as the scrutinee of a match with distinct branches *)
Definition lazy9 := Eval lazy in
  fun x : bool =>
    (fun (a : array bool) (y : bool) =>
       match get a 0 with true => x | false => y end) [| x | x |].
Definition cbv9 := Eval cbv in
  fun x : bool =>
    (fun (a : array bool) (y : bool) =>
       match get a 0 with true => x | false => y end) [| x | x |].
Check check_const_eq lazy9 (fun x y : bool => if x then x else y).
Check check_const_eq cbv9 (fun x y : bool => if x then x else y).

(* 10. under a fix *)
Fixpoint f (n : nat) (a : array bool) (y : bool) {struct n} : bool :=
  match n with O => get a 0 | S k => f k a y end.

Definition lazy10 := Eval lazy in
  fun x : bool => (fun (a : array bool) (y : bool) => f 3 a y) [| x | x |].
Definition cbv10 := Eval cbv in
  fun x : bool => (fun (a : array bool) (y : bool) => f 3 a y) [| x | x |].
Check check_const_eq lazy10 (fun x _ : bool => x).
Check check_const_eq cbv10 (fun x _ : bool => x).

(* 11. let-bound array, two binders deep *)
Definition lazy11 := Eval lazy in
  fun x : bool => let a := [| x | x |] in fun y z : bool => get a 0.
Definition cbv11 := Eval cbv in
  fun x : bool => let a := [| x | x |] in fun y z : bool => get a 0.
Check check_const_eq lazy11 (fun x _ _ : bool => x).
Check check_const_eq cbv11 (fun x _ _ : bool => x).

(* 12. array of arrays *)
Definition lazy12 := Eval lazy in
  fun x : bool =>
    (fun (a : array (array bool)) (y : bool) => get (get a 0) 0)
      [| [| x | x |] | [| x | x |] |].
Definition cbv12 := Eval cbv in
  fun x : bool =>
    (fun (a : array (array bool)) (y : bool) => get (get a 0) 0)
      [| [| x | x |] | [| x | x |] |].
Check check_const_eq lazy12 (fun x _ : bool => x).
Check check_const_eq cbv12 (fun x _ : bool => x).

(* 13. control: a primitive value that carries no subterm *)
Definition lazy13 := Eval lazy in
  fun x : float => (fun (a : float) (y : bool) => PrimFloat.add a a) 2%float.
Definition cbv13 := Eval cbv in
  fun x : float => (fun (a : float) (y : bool) => PrimFloat.add a a) 2%float.
Check check_const_eq lazy13 (fun (_ : float) (_ : bool) => 4%float).
Check check_const_eq cbv13 (fun (_ : float) (_ : bool) => 4%float).

(* Conversion, which uses the same machine, agrees. *)
Definition conv1 : (fun (x y : bool) => (fun (a : array bool) (z : bool) => get a 0) [| x | x |] y)
                   = (fun x _ : bool => x)
  := eq_refl.
Definition conv2 : (fun (x y : bool) => let a := [| x | x |] in get a 0) = (fun x _ : bool => x)
  := eq_refl.
