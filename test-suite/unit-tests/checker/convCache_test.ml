(* The unit cache of the native conversion (checker/convCache.ml).

   A worker whose cast runs past the VM budget publishes the code of the
   definitions its conversion needs; the other workers load it instead of
   compiling it again. The tests run real forked workers through
   [CheckWorkers] and read what each of them generated: a generated source
   defines a constant with a line [let const_<name> …], and names it with
   another unit's prefix when that unit defines it.

   What they check: a shared closure is compiled once even when the casts
   start together; a unit is not reused where one of its definitions has
   another body behind the same name; a unit whose file does not match the
   digest its producer published is refused; and every exit after a claim,
   the fallback to the VM included, releases the claim. *)

open OUnit
open Utest
open Coq_checklib
open Names

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let id = Id.of_string
let lam s body = Constr.mkLambda (Context.make_annot (Name.Name (id s)) Sorts.Relevant, Constr.mkProp, body)
let rel = Constr.mkRel
let app f args = Constr.mkApp (f, args)
let cst c = Constr.UnsafeMonomorphic.mkConst c

(* Church booleans; a cast's conversion test does not type its sides. *)
let tt = lam "t" (lam "f" (rel 2))
let ff = lam "t" (lam "f" (rel 1))

let flags =
  let f = Declareops.safe_flags Conv_oracle.empty in
  { f with Declarations.enable_VM = true; enable_native_compiler = true }

let constant_of name =
  Constant.make2 (ModPath.MPfile (DirPath.make [id "ConvCacheTest"])) (id name)

(* A constant with its bytecode, as the checker holds one: the VM decides
   the cast when the native code cannot be built. *)
let add_constant c body env =
  let def = Declarations.Def body in
  let vmtab = Environ.vm_library env in
  let vmtab, code =
    match Vmbytegen.compile_constant_body ~fail_on_error:true env Declarations.Monomorphic def with
    | Some (Vmemitcodes.BCdefined (mask, code, patches)) ->
      let vmtab, index = Vmlibrary.add code vmtab in
      vmtab, Some (Vmemitcodes.BCdefined (mask, index, patches))
    | Some (Vmemitcodes.BCalias _ | Vmemitcodes.BCconstant) | None ->
      assert_failure (Constant.to_string c ^ " did not compile to bytecode")
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

(* An environment holding a chain [<name>1 … <name>8], each the previous
   one applied twice, and one small [user] constant per index of [users],
   each naming the last of the chain. The chain is the closure the casts
   share and the workers must compile once; a user is the small part a
   worker owns. [negate] chooses the first link: negation, or the identity
   written the same way. Both leave [user tt] convertible to [tt]. *)
let shared_env ?(negate = true) ~users name =
  let first = if negate then lam "b" (app (rel 1) [| ff; tt |])
    else lam "b" (app (rel 1) [| tt; ff |]) in
  let link i = constant_of (Printf.sprintf "%s%d" name i) in
  let base =
    let env = Environ.set_typing_flags flags Environ.empty_env in
    Environ.set_vm_library
      (Vmlibrary.set_path (DirPath.make [id "ConvCacheTest"]) (Environ.vm_library env)) env
  in
  let env = add_constant (link 1) first base in
  let env = ref env in
  for i = 2 to 8 do
    let prev = cst (link (i - 1)) in
    env := add_constant (link i) (lam "b" (app prev [| app prev [| rel 1 |] |])) !env
  done;
  let last = cst (link 8) in
  let users =
    List.map (fun i ->
        let u = constant_of (Printf.sprintf "%s_user%d" name i) in
        env := add_constant u (lam "b" (app last [| rel 1 |])) !env;
        u)
      users
  in
  !env, users

let check_cast env t1 t2 () =
  Typeops.check_cast env (Environ.make_judge Constr.mkProp t1) Constr.VMcast
    { Environ.utj_val = t2; utj_type = Sorts.prop }

(* The cast of [u]: [u tt] against [tt], which only computation decides.
   Each link applies its predecessor twice, so the chain computes the
   identity whichever first link it has. *)
let cast_of env u = check_cast env (app (cst u) [| tt |]) tt

(** {6 Reading what the workers left behind} *)

let temp_dir = Filename.concat (Filename.get_temp_dir_name ()) "convCache_test"

let rec files_under dir suffix =
  Array.fold_left (fun acc f ->
      let f = Filename.concat dir f in
      if Sys.is_directory f then files_under f suffix @ acc
      else if Filename.check_suffix f suffix then f :: acc
      else acc)
    [] (Sys.readdir dir)

let contains text sub =
  let n = String.length text and m = String.length sub in
  let rec go i = i + m <= n && (String.equal (String.sub text i m) sub || go (i + 1)) in
  go 0

let defines file name =
  let ch = open_in file in
  let rec go () = match input_line ch with
    | line ->
      let prefix = "let const_" in
      if String.length line > String.length prefix
      && String.equal (String.sub line 0 (String.length prefix)) prefix
      && contains line name
      then true else go ()
    | exception End_of_file -> false
  in
  Fun.protect ~finally:(fun () -> close_in ch) go

(* The generated name of a constant escapes its label: '_' becomes "__"
   (see "Printing to ocaml" in nativecode.ml). *)
let escaped name =
  String.concat "" (List.map (fun c -> if c = '_' then "__" else String.make 1 c)
                      (List.init (String.length name) (String.get name)))

let definitions name =
  let name = escaped name in
  List.filter (fun f -> defines f name) (files_under temp_dir ".native")

let claims () = files_under temp_dir ".claim"
let manifests () = files_under temp_dir ".manifest"
let cmxs () = List.filter (fun f -> not (contains f "/other/")) (files_under temp_dir ".cmxs")

(** {6 Running casts in workers} *)

let proof = ref 0

let run ?(jobs = 4) casts =
  CheckWorkers.set_jobs ~profiling:false jobs;
  Fun.protect ~finally:(fun () -> CheckWorkers.set_jobs ~profiling:false 1) @@ fun () ->
  let result =
    try
      List.iter (fun check ->
          incr proof;
          CheckWorkers.defer ~vm_cast:true (constant_of (Printf.sprintf "proof%d" !proof)) check)
        casts;
      CheckWorkers.finish (); None
    with e -> CheckWorkers.abort (); Some e
  in
  match result with
  | None -> ()
  | Some e -> assert_failure ("a worker failed: " ^ Printexc.to_string e)

let kernel_cmi_dir () =
  let ocamlfind = Boot.Env.ocamlfind () in
  let ch = Unix.open_process_args_in ocamlfind [| ocamlfind; "query"; "rocq-runtime.kernel" |] in
  let dir = input_line ch in
  match Unix.close_process_in ch with
  | Unix.WEXITED 0 -> dir
  | _ -> assert_failure "ocamlfind query rocq-runtime.kernel failed"

let rec remove_tree f =
  if Sys.file_exists f then
    if Sys.is_directory f then begin
      Array.iter (fun g -> remove_tree (Filename.concat f g)) (Sys.readdir f);
      Unix.rmdir f
    end else Sys.remove f

(* Everything the workers generate must stay for the test to read it, and
   land under a directory of the test's own, which goes at exit. Workers
   end with [Unix._exit], so only this process removes it. *)
let () =
  remove_tree temp_dir;
  Unix.mkdir temp_dir 0o700;
  let me = Unix.getpid () in
  at_exit (fun () -> if Unix.getpid () = me then try remove_tree temp_dir with _ -> ());
  Filename.set_temp_dir_name temp_dir;
  CDebug.set_flags "native-compiler";
  Nativecode.set_native_vm_conversion true;
  Nativelib.include_dirs := [kernel_cmi_dir ()];
  Nativelib.get_load_paths := (fun () -> []);
  Nativelib.force_temp_dir ();
  (* Every cast takes the native path at once, as a cast past its VM
     budget does. *)
  Typeops.set_native_conversion_after 0.;
  CheckWorkers.set_budget 60.;
  (* The last test takes the compiler away for a moment. OUnit fails a
     test that changes the environment, so the variable exists from the
     start. *)
  Unix.putenv "OCAMLFIND" (Boot.Env.ocamlfind ());
  CheckWorkers.set_jobs ~profiling:false 4;
  ConvCache.enable ();
  CheckWorkers.set_jobs ~profiling:false 1

let () = add_test "the cache is on with workers" (fun () ->
  assert_bool "the cache did not turn on" (ConvCache.is_enabled ()))

let () = add_test "without the cache, every worker compiles the shared closure" (fun () ->
  (* What the checker did before this step: each cast's own unit holds
     the whole closure of its conversion. *)
  let saved = !Nativelib.prepare_conversion in
  Nativelib.prepare_conversion := (fun _ _ _ -> ());
  Fun.protect ~finally:(fun () -> Nativelib.prepare_conversion := saved) (fun () ->
      let env, users = shared_env ~users:[1; 2; 3] "depnocache" in
      run (List.map (fun u -> cast_of env u) users));
  assert_equal ~msg:"units defining the last link of the shared chain" ~printer:string_of_int
    3 (List.length (definitions "depnocache8")))

let () = add_test "casts that start together compile their shared closure once" (fun () ->
  let env, users = shared_env ~users:[1; 2; 3] "depshared" in
  run (List.map (fun u -> cast_of env u) users);
  assert_equal ~msg:"units defining the last link of the shared chain" ~printer:string_of_int
    1 (List.length (definitions "depshared8"));
  assert_bool "nothing was published" (not (CList.is_empty (manifests ())));
  assert_bool "a claim was left behind" (CList.is_empty (claims ())))

let () = add_test "a unit is not reused where a name has another body" (fun () ->
  (* Two checks of one name: the chains differ in their first link only,
     and the user constants are the same declaration in both. A consumer
     that took the other check's code would run the other chain. *)
  let env, users = shared_env ~users:[1] "depbody" in
  run [cast_of env (List.hd users)];
  assert_equal ~msg:"the first check compiled its own user constant" ~printer:string_of_int
    1 (List.length (definitions "depbody_user1"));
  let env', users' = shared_env ~negate:false ~users:[1] "depbody" in
  run [cast_of env' (List.hd users')];
  assert_equal ~msg:"units defining the user constant after the second check"
    ~printer:string_of_int 2 (List.length (definitions "depbody_user1")))

let () = add_test "a unit whose file does not match its digest is refused" (fun () ->
  let env, users = shared_env ~users:[1] "deptampered" in
  run [cast_of env (List.hd users)];
  assert_equal ~msg:"the producer compiled the chain" ~printer:string_of_int
    1 (List.length (definitions "deptampered8"));
  (* Replace every published unit with one that is valid OCaml and has
     the very module name the loader expects, so that only the digest
     the producer published tells them apart. *)
  let dir = Filename.concat temp_dir "other" in
  (try Unix.mkdir dir 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  let replace f =
    let base = Filename.remove_extension (Filename.basename f) in
    let ml = Filename.concat dir (base ^ ".ml") in
    let ch = open_out ml in
    output_string ch "let () = ()\n";
    close_out ch;
    let out = Filename.concat dir (base ^ ".cmxs") in
    (match CUnix.sys_command (Boot.Env.ocamlfind ())
             ["opt"; "-shared"; "-o"; out; "-impl"; ml] with
     | Unix.WEXITED 0 -> ()
     | Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _ ->
       assert_failure "could not compile the replacement unit");
    let ic = open_in_bin out and oc = open_out_bin f in
    output_string oc (really_input_string ic (in_channel_length ic));
    close_in ic; close_out oc
  in
  List.iter replace (cmxs ());
  (* A second cast over the same chain must refuse the unit and compile
     the chain again. *)
  let env', users' = shared_env ~users:[2] "deptampered" in
  run [cast_of env' (List.hd users')];
  assert_equal ~msg:"units defining the chain after the refusal"
    ~printer:string_of_int 2 (List.length (definitions "deptampered8")))

let () = add_test "a worker that falls back to the VM leaves no claim" (fun () ->
  (* With no compiler, no unit can be built: the worker releases its
     claims and the cast falls back to the VM, which decides it. *)
  let env, users = shared_env ~users:[1; 2] "depnocompiler" in
  let real = Unix.getenv "OCAMLFIND" in
  Unix.putenv "OCAMLFIND" "/bin/false";
  Fun.protect
    ~finally:(fun () -> Unix.putenv "OCAMLFIND" real)
    (fun () -> run (List.map (fun u -> cast_of env u) users));
  assert_bool "a claim was left behind" (CList.is_empty (claims ())))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
