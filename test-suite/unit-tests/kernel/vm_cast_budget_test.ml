(* While coqchk decides VM casts with native code
   ([Nativecode.set_native_vm_conversion true]), [Typeops.check_cast] runs
   the VM first, for at most [Typeops.set_native_conversion_after] seconds
   of wall-clock time. A VM verdict reached within that budget is final.
   When the budget runs out, the VM gives no verdict and native code
   decides the cast. Budget 0 decides with native code at once.

   Which one decided is seen from the native compiler's links: a native
   conversion compiles the constant [cnot] that the cast unfolds into its
   unit and marks it [Linked] once the unit is loaded; the VM never
   touches that mark. *)

open OUnit
open Utest
open Names

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let id = Id.of_string
let lam s body = Constr.mkLambda (Context.make_annot (Name.Name (id s)) Sorts.Relevant, Constr.mkProp, body)
let app f args = Constr.mkApp (f, args)
let rel = Constr.mkRel

(* Church booleans and numerals. A cast's conversion test does not type
   its two sides, so the binder types do not matter. *)
let tt = lam "t" (lam "f" (rel 2))
let ff = lam "t" (lam "f" (rel 1))

let church k =
  let rec apply_f i = if i = 0 then rel 1 else app (rel 2) [| apply_f (i - 1) |] in
  lam "f" (lam "x" (apply_f k))

let dp = DirPath.make [id "VmCastBudgetTest"]
let cnot = Constant.make2 (ModPath.MPfile dp) (id "cnot")

(* An environment with [cnot := fun b => b ff tt], and its bytecode, as
   the checker compiles it ([Mod_checking.compile_constant_bytecode]). Each
   call gives [cnot] a fresh link mark. *)
let make_env () =
  let flags = Declareops.safe_flags Conv_oracle.empty in
  let flags = { flags with Declarations.enable_VM = true; enable_native_compiler = true } in
  let env = Environ.set_typing_flags flags Environ.empty_env in
  let body = Declarations.Def (lam "b" (app (rel 1) [| ff; tt |])) in
  let vmtab = Vmlibrary.set_path dp (Environ.vm_library env) in
  let vmtab, code =
    match Vmbytegen.compile_constant_body ~fail_on_error:true env Declarations.Monomorphic body with
    | Some (Vmemitcodes.BCdefined (mask, code, patches)) ->
      let vmtab, index = Vmlibrary.add code vmtab in
      vmtab, Some (Vmemitcodes.BCdefined (mask, index, patches))
    | Some (Vmemitcodes.BCalias _ | Vmemitcodes.BCconstant) | None ->
      assert_failure "cnot did not compile to bytecode"
  in
  let cb = {
    Declarations.const_hyps = [];
    const_univ_hyps = UVars.Instance.empty;
    const_body = body;
    const_type = Constr.mkProp;
    const_relevance = Sorts.Relevant;
    const_body_code = code;
    const_universes = Declarations.Monomorphic;
    const_inline_code = false;
    const_typing_flags = flags;
  } in
  Environ.add_constant cnot cb (Environ.set_vm_library vmtab env)

let linked env =
  let _, (link, _), _ = Environ.lookup_constant_key cnot env in
  match !link with
  | Environ.NotLinked -> false
  | Environ.Linked _ -> true

(* [parity k] negates [tt] 2^k times: it is [tt], after 2^k steps. *)
let parity k = app (church k) [| church 2; Constr.UnsafeMonomorphic.mkConst cnot; tt |]

(* Whether the VM cast of [t1] to [t2] is accepted. *)
let accepts env t1 t2 =
  match Typeops.check_cast env (Environ.make_judge Constr.mkProp t1) Constr.VMcast
          { Environ.utj_val = t2; utj_type = Sorts.prop } with
  | () -> true
  | exception Type_errors.TypeError _ -> false

let kernel_cmi_dir () =
  let ocamlfind = Boot.Env.ocamlfind () in
  let ch = Unix.open_process_args_in ocamlfind [| ocamlfind; "query"; "rocq-runtime.kernel" |] in
  let dir = input_line ch in
  match Unix.close_process_in ch with
  | Unix.WEXITED 0 -> dir
  | _ -> assert_failure "ocamlfind query rocq-runtime.kernel failed"

let () =
  Nativecode.set_native_vm_conversion true;
  Nativelib.include_dirs := [kernel_cmi_dir ()];
  Nativelib.get_load_paths := (fun () -> [])

(* The VM takes seconds on [parity long]; native code a fraction of one. *)
let long = 25

let () = add_test "the VM decides a cast within its budget" (fun () ->
  Typeops.set_native_conversion_after 60.;
  let env = make_env () in
  assert_bool "parity 4 = tt was rejected" (accepts env (parity 4) tt);
  assert_bool "parity 4 = ff was accepted" (not (accepts env (parity 4) ff));
  assert_bool "native code decided a cast the VM finished within its budget" (not (linked env)))

let () = add_test "native code decides a cast the VM did not finish within its budget" (fun () ->
  Typeops.set_native_conversion_after 0.05;
  let env = make_env () in
  assert_bool "parity 25 = tt was rejected" (accepts env (parity long) tt);
  assert_bool "native code did not decide" (linked env);
  let env = make_env () in
  assert_bool "parity 25 = ff was accepted" (not (accepts env (parity long) ff));
  assert_bool "native code did not decide" (linked env))

let () = add_test "budget 0 decides with native code at once" (fun () ->
  Typeops.set_native_conversion_after 0.;
  let env = make_env () in
  assert_bool "parity 4 = tt was rejected" (accepts env (parity 4) tt);
  assert_bool "native code did not decide" (linked env))

let () = add_test "the VM decides correctly after a budget interrupted it" (fun () ->
  Typeops.set_native_conversion_after 0.01;
  let env = make_env () in
  assert_bool "parity 25 = tt was rejected" (accepts env (parity long) tt);
  assert_bool "the VM was not interrupted" (linked env);
  Typeops.set_native_conversion_after 60.;
  let env = make_env () in
  assert_bool "parity 20 = tt was rejected" (accepts env (parity 20) tt);
  assert_bool "parity 20 = ff was accepted" (not (accepts env (parity 20) ff));
  assert_bool "native code decided a cast the VM finished within its budget" (not (linked env));
  (* And without a budget, as when native code fails. *)
  let vm t = Vconv.vm_conv Conversion.CUMUL env (parity 22) t in
  assert_bool "the VM rejected parity 22 = tt" (Result.is_ok (vm tt));
  assert_bool "the VM accepted parity 22 = ff" (Result.is_error (vm ff)))

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
