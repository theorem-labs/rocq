(* What the unit cache of the native conversion (checker/convCache.ml) may
   reuse, between two workers whose environments differ.

   1. Two kernel names that print the same are two definitions. A kernel
      identifier read from an object may hold any bytes, '.' included: a
      constant [c] of the module [Top.A.B] and a constant whose label is
      the identifier ["B.c"] of the module [Top.A] both print [Top.A.B.c],
      while the environment keeps them apart. A cache keyed on the printed
      name would give one's code to the other.
   2. Two constants with one user name and different canonical names, and
      the same transparent body, are one definition: the environment and
      the generated code take them for one, and their code keeps no
      canonical name, so a worker reuses what another published.
   3. But the code of an axiom (an accumulator) keeps its canonical name,
      which the conversion compares. Two axioms with one user name and
      different canonical names must not share code, or a worker would
      accept a conversion that native and VM conversion both reject.

   Every cast runs natively in a forked child, as a worker runs it, with
   the [native-conversion-failed] warning made an error: a cast that
   falls back to the VM fails the test, so a verdict always comes from
   the native code and the cache. Each child also reports which unit each
   definition of interest is linked to, which shows what it reused. *)

open OUnit
open Utest
open Coq_checklib
open Names

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let id = Id.of_string

(* An identifier with bytes the parser would refuse, as a .vo file can
   hold it: [Id.t] is a string that [Id.of_string] would check. *)
let raw_id (s : string) : Id.t = Obj.magic s

let lam s body = Constr.mkLambda (Context.make_annot (Name.Name (id s)) Sorts.Relevant, Constr.mkProp, body)
let rel = Constr.mkRel
let app f args = Constr.mkApp (f, args)
let cst c = Constr.UnsafeMonomorphic.mkConst c

let tt = lam "t" (lam "f" (rel 2))
let ff = lam "t" (lam "f" (rel 1))

let flags =
  let f = Declareops.safe_flags Conv_oracle.empty in
  { f with Declarations.enable_VM = true; enable_native_compiler = true }

let dp = DirPath.make [id "Top"]
let mp_a = ModPath.MPdot (ModPath.MPfile dp, id "A")
let mp_a_b = ModPath.MPdot (mp_a, id "B")

let empty_env () =
  let env = Environ.set_typing_flags flags Environ.empty_env in
  Environ.set_vm_library (Vmlibrary.set_path dp (Environ.vm_library env)) env

(* A constant of type [Prop] with its bytecode, as the checker holds one. *)
let add_constant c def env =
  let vmtab = Environ.vm_library env in
  let vmtab, code =
    match Vmbytegen.compile_constant_body ~fail_on_error:true env Declarations.Monomorphic def with
    | Some (Vmemitcodes.BCdefined (mask, code, patches)) ->
      let vmtab, index = Vmlibrary.add code vmtab in
      vmtab, Some (Vmemitcodes.BCdefined (mask, index, patches))
    | Some (Vmemitcodes.BCalias _ as c) | Some (Vmemitcodes.BCconstant as c) -> vmtab, Some c
    | None -> vmtab, None
  in
  let cb = {
    Declarations.const_hyps = [];
    const_univ_hyps = UVars.Instance.empty;
    const_body = def;
    const_type = Constr.mkProp;
    const_relevance = Sorts.Relevant;
    const_body_code = code;
    const_universes = Declarations.Monomorphic;
    const_inline_code = false;
    const_typing_flags = flags;
  } in
  Environ.add_constant c cb (Environ.set_vm_library vmtab env)

let define c body env = add_constant c (Declarations.Def body) env
let axiom c env = add_constant c (Declarations.Undef None) env

(* [negation]: [fun b => b ff tt]; [identity]: [fun b => b tt ff]. Both
   are closed and compute on Church booleans. *)
let negation = lam "b" (app (rel 1) [| ff; tt |])
let identity = lam "b" (app (rel 1) [| tt; ff |])

let check_cast env t1 t2 =
  Typeops.check_cast env (Environ.make_judge Constr.mkProp t1) Constr.VMcast
    { Environ.utj_val = t2; utj_type = Sorts.prop }

(** {6 Running a cast as a worker} *)

let temp_dir = Filename.concat (Filename.get_temp_dir_name ()) "convCacheIdentity_test"

type outcome = {
  verdict : int;              (* 0 accepted, 1 rejected, 2 any other failure *)
  prefixes : string list;     (* the unit each definition is linked to, "-" if none *)
}

(* The cast [t1] to [t2] in a forked child. After it, the child reports
   the unit each of [defs] is linked to. With [~no_compiler], the child
   has no OCaml compiler, so its native code cannot be built. *)
let run ?(no_compiler = false) env t1 t2 defs =
  let result = Filename.temp_file ~temp_dir "result" "" in
  match Unix.fork () with
  | 0 ->
    if no_compiler then Unix.putenv "OCAMLFIND" "/bin/false";
    let code = match check_cast env t1 t2 with
      | () -> 0
      | exception Type_errors.TypeError _ -> 1
      | exception _ -> 2
    in
    let ch = open_out result in
    List.iter (fun d ->
        output_string ch
          (Option.default "-" (Nativecode.definition_prefix env (Nativecode.Dconst d)) ^ "\n"))
      defs;
    close_out ch;
    Unix._exit code
  | pid ->
    let verdict = match snd (Unix.waitpid [] pid) with
      | Unix.WEXITED n -> n
      | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> 3
    in
    let ch = open_in result in
    let prefixes = List.map (fun _ -> try input_line ch with End_of_file -> "?") defs in
    close_in ch;
    { verdict; prefixes }

let rec files_under dir suffix =
  Array.fold_left (fun acc f ->
      let f = Filename.concat dir f in
      if Sys.is_directory f then files_under f suffix @ acc
      else if Filename.check_suffix f suffix then f :: acc
      else acc)
    [] (Sys.readdir dir)

let manifests () = List.length (files_under temp_dir ".manifest")

let rec remove_tree f =
  if Sys.file_exists f then
    if Sys.is_directory f then begin
      Array.iter (fun g -> remove_tree (Filename.concat f g)) (Sys.readdir f);
      Unix.rmdir f
    end else Sys.remove f

let kernel_cmi_dir () =
  let ocamlfind = Boot.Env.ocamlfind () in
  let ch = Unix.open_process_args_in ocamlfind [| ocamlfind; "query"; "rocq-runtime.kernel" |] in
  let dir = input_line ch in
  match Unix.close_process_in ch with
  | Unix.WEXITED 0 -> dir
  | _ -> assert_failure "ocamlfind query rocq-runtime.kernel failed"

let () =
  remove_tree temp_dir;
  Unix.mkdir temp_dir 0o700;
  let me = Unix.getpid () in
  at_exit (fun () -> if Unix.getpid () = me then try remove_tree temp_dir with _ -> ());
  Filename.set_temp_dir_name temp_dir;
  CDebug.set_flags "native-compiler";
  (* A cast whose native code cannot be built or loaded falls back to the
     VM after this warning; here it fails instead. *)
  CWarnings.set_flags "+native-conversion-failed";
  Nativecode.set_native_vm_conversion true;
  Nativelib.include_dirs := [kernel_cmi_dir ()];
  Nativelib.get_load_paths := (fun () -> []);
  Nativelib.force_temp_dir ();
  Typeops.set_native_conversion_after 0.;
  CheckWorkers.set_jobs ~profiling:false 4;
  ConvCache.enable ();
  CheckWorkers.set_jobs ~profiling:false 1

let () = add_test "a cast that falls back to the VM fails the run" (fun () ->
  (* The VM would accept this cast; without a compiler the native code
     cannot be built, and the warning made an error stops the cast. So no
     test above can pass through the VM. *)
  let k = Constant.make2 mp_a (id "fallback") in
  let o = run ~no_compiler:true (define k negation (empty_env ())) (app (cst k) [| tt |]) ff [k] in
  assert_equal ~printer:string_of_int ~msg:"the verdict of a cast that fell back" 2 o.verdict)

let pp_outcome o = Printf.sprintf "verdict %d, linked to %s" o.verdict (String.concat " " o.prefixes)

(** {6 1. Two kernel names that print the same} *)

let c_inner = Constant.make2 mp_a_b (id "c")           (* module Top.A.B, label c *)
let c_outer = Constant.make2 mp_a (raw_id "B.c")       (* module Top.A, label "B.c" *)

let () = add_test "two kernel names that print the same are two definitions" (fun () ->
  assert_bool "the cache did not turn on" (ConvCache.is_enabled ());
  assert_equal ~printer:(fun s -> s) ~msg:"the two names print the same"
    (Constant.to_string c_inner) (Constant.to_string c_outer);
  (* [c_inner (c_outer tt)] against [tt]: true where [c_outer] is the
     negation, false where it is the identity. *)
  let cast = app (cst c_inner) [| app (cst c_outer) [| tt |] |] in
  let env outer = define c_outer outer (define c_inner negation (empty_env ())) in
  let before = manifests () in
  let producer = run (env negation) cast tt [c_outer] in
  assert_equal ~printer:pp_outcome ~msg:"the producer accepts, natively"
    { verdict = 0; prefixes = producer.prefixes } producer;
  assert_bool "the producer published no unit" (manifests () > before);
  let consumer = run (env identity) cast tt [c_outer] in
  assert_equal ~printer:string_of_int ~msg:"the consumer rejects, natively" 1 consumer.verdict;
  assert_bool "the consumer's c_outer is linked to the producer's code"
    (not (String.equal (List.hd consumer.prefixes) (List.hd producer.prefixes))))

(** {6 2. One user name, different canonical names, a transparent body} *)

let user_kn = KerName.make mp_a (id "aliased")
let k_one = Constant.make user_kn (KerName.make (ModPath.MPfile (DirPath.make [id "One"])) (id "aliased"))
let k_two = Constant.make user_kn (KerName.make (ModPath.MPfile (DirPath.make [id "Two"])) (id "aliased"))

let () = add_test "one user name with a transparent body is one definition, reused" (fun () ->
  assert_bool "the canonical names are equal"
    (not (KerName.equal (Constant.canonical k_one) (Constant.canonical k_two)));
  let cast k = app (cst k) [| tt |] in
  let producer = run (define k_one negation (empty_env ())) (cast k_one) ff [k_one] in
  assert_equal ~printer:string_of_int ~msg:"the producer accepts, natively" 0 producer.verdict;
  let consumer = run (define k_two negation (empty_env ())) (cast k_two) ff [k_two] in
  assert_equal ~printer:string_of_int ~msg:"the consumer accepts, natively" 0 consumer.verdict;
  assert_equal ~printer:(fun s -> s) ~msg:"the consumer reused the producer's code"
    (List.hd producer.prefixes) (List.hd consumer.prefixes))

(** {6 3. One user name, different canonical names, an axiom}

    The review's counterexample. Both environments hold two independent
    axioms [A.x] and [B.x], and an axiom [u] of user name [U.x], whose
    canonical name is [A.x] in the producer and [B.x] in the consumer. *)

let kn_of m l = KerName.make (ModPath.MPfile (DirPath.make [id m])) (id l)
let a_x = Constant.make1 (kn_of "A" "x")
let b_x = Constant.make1 (kn_of "B" "x")
let u_producer = Constant.make (kn_of "U" "x") (kn_of "A" "x")
let u_consumer = Constant.make (kn_of "U" "x") (kn_of "B" "x")

let axioms u = axiom u (axiom b_x (axiom a_x (empty_env ())))

(* [(fun z => z) t]: a redex, so the conversion does not stop at syntactic
   equality. *)
let redex t = app (lam "z" (rel 1)) [| t |]

let () = add_test "an axiom's code is not reused where its canonical name differs" (fun () ->
  let before = manifests () in
  let producer = run (axioms u_producer) (redex (cst u_producer)) (cst u_producer) [u_producer] in
  assert_equal ~printer:string_of_int ~msg:"the producer accepts u against u, natively" 0 producer.verdict;
  assert_bool "the producer published no unit" (manifests () > before);
  (* In the consumer, [u] is [B.x], not [A.x]. *)
  let consumer = run (axioms u_consumer) (redex (cst u_consumer)) (cst a_x) [u_consumer] in
  assert_equal ~printer:string_of_int ~msg:"the consumer rejects u against A.x, natively" 1 consumer.verdict;
  assert_bool "the consumer's u is linked to the producer's code"
    (not (String.equal (List.hd consumer.prefixes) (List.hd producer.prefixes))))

let () = add_test "an axiom's code is reused where its canonical name is the same" (fun () ->
  (* The same two environments, but the canonical names agree: the
     consumer reuses the producer's code for [u], and its verdict stands. *)
  let u = Constant.make (kn_of "V" "x") (kn_of "A" "x") in
  let producer = run (axioms u) (redex (cst u)) (cst u) [u] in
  assert_equal ~printer:string_of_int ~msg:"the producer accepts u against u, natively" 0 producer.verdict;
  let consumer = run (axioms u) (redex (cst u)) (cst a_x) [u] in
  assert_equal ~printer:string_of_int ~msg:"the consumer accepts u against A.x, natively" 0 consumer.verdict;
  assert_equal ~printer:(fun s -> s) ~msg:"the consumer reused the producer's code"
    (List.hd producer.prefixes) (List.hd consumer.prefixes))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
