(* While coqchk decides VM casts with native code, a conversion whose unit
   the OCaml compiler or the dynamic linker rejects is not decided
   natively: [Nativeconv.native_cast_conv] returns [None], after a
   [native-conversion-failed] warning, so that [Typeops.check_cast] decides
   the cast with the VM. The constants that the unit was to define stay
   [NotLinked]: OCaml cannot unload a unit that failed inside
   [Dynlink.loadfile], so a later unit must compile them again rather than
   refer to the dead one. *)

open OUnit
open Utest
open Names

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let id = Id.of_string

(* [c := fun x : Prop => x], in an environment where the native compiler
   is on. *)
let c = Constant.make2 (ModPath.MPfile (DirPath.make [id "Top"])) (id "c")

let env =
  let annot = Context.make_annot (Name.Name (id "x")) Sorts.Relevant in
  let body = Constr.mkLambda (annot, Constr.mkProp, Constr.mkRel 1) in
  let cb = {
    Declarations.const_hyps = [];
    const_univ_hyps = UVars.Instance.empty;
    const_body = Declarations.Def body;
    const_type = Constr.mkProp;
    const_relevance = Sorts.Relevant;
    const_body_code = None;
    const_universes = Declarations.Monomorphic;
    const_inline_code = false;
    const_typing_flags = Declareops.safe_flags Conv_oracle.empty;
  } in
  let env = Environ.empty_env in
  let env = Environ.set_typing_flags
      { (Environ.typing_flags env) with Declarations.enable_native_compiler = true } env in
  Environ.add_constant c cb env

let linked () =
  let _, (link, _), _ = Environ.lookup_constant_key c env in
  match !link with
  | Environ.NotLinked -> false
  | Environ.Linked _ -> true

(* [c s] against [s]: not equal as terms, so deciding them takes a unit
   that defines [c]. *)
let decide s =
  let t1 = Constr.mkApp (Constr.UnsafeMonomorphic.mkConst c, [| s |]) in
  Nativecode.set_native_vm_conversion true;
  Nativelib.get_load_paths := (fun () -> []);
  Nativeconv.native_cast_conv Conversion.CUMUL (Genlambda.empty_evars env) env t1 s

let real_ocamlfind = Boot.Env.ocamlfind ()

let kernel_cmi_dir () =
  let ch = Unix.open_process_args_in real_ocamlfind [| real_ocamlfind; "query"; "rocq-runtime.kernel" |] in
  let dir = input_line ch in
  match Unix.close_process_in ch with
  | Unix.WEXITED 0 -> dir
  | _ -> assert_failure "ocamlfind query rocq-runtime.kernel failed"

(* An OCAMLFIND that runs the real one, then overwrites the first unit it
   makes with bytes that [Dynlink.loadfile] refuses. It is set before the
   tests run: OUnit fails a test that changes the environment. A compile
   that fails makes no unit, so the first test leaves it armed. *)
let corrupting_ocamlfind () =
  let dir = Filename.temp_file "nativeconv_fallback" "" in
  Sys.remove dir;
  Unix.mkdir dir 0o700;
  let script = Filename.concat dir "ocamlfind" in
  let mark = Filename.concat dir "corrupted" in
  let ch = open_out script in
  Printf.fprintf ch "#!/bin/sh\n%s \"$@\" || exit $?\n\
                     if [ ! -e %s ]; then\n  : > %s\n\
                     \  prev=; for a in \"$@\"; do [ \"$prev\" = -o ] && out=$a; prev=$a; done\n\
                     \  printf garbage > \"$out\"\nfi\n"
    (Filename.quote real_ocamlfind) (Filename.quote mark) (Filename.quote mark);
  close_out ch;
  Unix.chmod script 0o755;
  at_exit (fun () ->
      List.iter (fun f -> if Sys.file_exists f then Sys.remove f) [script; mark];
      Unix.rmdir dir);
  script

let () = Unix.putenv "OCAMLFIND" (corrupting_ocamlfind ())

let () = add_test "a unit that fails to compile is not decided and links nothing" (fun () ->
  (* The include directory, which must hold the kernel's .cmi files, does
     not exist, so the OCaml compiler fails on the unit. *)
  Nativelib.include_dirs := [Filename.concat (Filename.get_temp_dir_name ()) "no-rocq-kernel-cmi-here"];
  match decide Constr.mkProp with
  | Some _ -> assert_failure "a conversion whose unit did not compile was decided natively"
  | None -> assert_bool "c is linked to a unit that did not compile" (not (linked ())))

let () = add_test "a unit that fails to load links nothing, and the next unit compiles it again" (fun () ->
  Nativelib.include_dirs := [kernel_cmi_dir ()];
  begin match decide Constr.mkProp with
  | Some _ -> assert_failure "a conversion whose unit did not load was decided natively"
  | None -> assert_bool "c is linked to a unit that did not load" (not (linked ()))
  end;
  (* Had c stayed linked to the dead unit, this unit would refer to it,
     and fail to load too. *)
  match decide Constr.mkSet with
  | Some (Result.Ok ()) -> assert_bool "c is not linked to the unit that loaded" (linked ())
  | Some (Result.Error ()) -> assert_failure "c Set and Set were found not convertible"
  | None -> assert_failure "the unit after a failed load was not decided natively")

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
