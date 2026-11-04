(* Unit tests of the rule that decides which constant bodies the VM compiler expands at an
   application site (Genlambda.inlinable_body), and of the counter of constants compiled again
   (Vmsymtable.compiled_again). The kernel here is the proof checker's type checker, not an
   operating system. *)

open OUnit
open Utest

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

(* Terms are built with the kernel's own constructors; no environment is needed, because
   [inlinable_body] reads the term only. *)
let anon = Context.annotR Names.Anonymous
let t_set = Constr.mkSort Sorts.set
let rel i = Constr.mkRel i
let lam body = Constr.mkLambda (anon, t_set, body)
let app f args = Constr.mkApp (f, args)

(* A chain of applications of the bound variable, [n] nodes deep. *)
let rec chain n = if n <= 0 then rel 1 else app (rel 1) [| chain (n - 1) |]

let () = add_test "a small function body is inlinable" (fun () ->
  assert_bool "fun x => x" (Genlambda.inlinable_body ~limit:50 (lam (rel 1))))

let () = add_test "a body that is not a function is not inlinable" (fun () ->
  assert_bool "a constant that is not a function"
    (not (Genlambda.inlinable_body ~limit:50 (app (rel 1) [| rel 2 |]))))

let () = add_test "a body over the limit is not inlinable" (fun () ->
  let big = lam (chain 100) in
  assert_bool "100 applications under a lambda, limit 50"
    (not (Genlambda.inlinable_body ~limit:50 big));
  assert_bool "the same body under a limit of 500"
    (Genlambda.inlinable_body ~limit:500 big))

let () = add_test "a limit of zero inlines nothing" (fun () ->
  assert_bool "fun x => x, limit 0"
    (not (Genlambda.inlinable_body ~limit:0 (lam (rel 1)))))

let () = add_test "a recursive body is not inlinable" (fun () ->
  (* fun (x : Set) => (fix f (y : Set) {struct y} := y) x: expanding it would copy the loop. *)
  let fix =
    Constr.mkFix (([| 0 |], 0), ([| anon |], [| Constr.mkProd (anon, t_set, t_set) |], [| rel 1 |]))
  in
  let body = lam (app fix [| rel 1 |]) in
  assert_bool "the body holds a fix" (not (Genlambda.inlinable_body ~limit:50 body));
  let cofix =
    Constr.mkCoFix (0, ([| anon |], [| Constr.mkProd (anon, t_set, t_set) |], [| rel 1 |]))
  in
  assert_bool "the body holds a cofix"
    (not (Genlambda.inlinable_body ~limit:50 (lam (app cofix [| rel 1 |])))))

let () = add_test "nothing is compiled again before a VM evaluation" (fun () ->
  assert_equal ~printer:string_of_int 0 (Vmsymtable.compiled_again ()))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
