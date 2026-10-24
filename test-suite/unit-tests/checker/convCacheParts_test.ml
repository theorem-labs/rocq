(* Dependency units compiled as parts (kernel/nativelib.ml,
   [compile_unit]; checker/convCache.ml).

   What the tests check:
   - a unit cut into several parts gives the verdicts of the unit in one
     module, natively, and another worker reuses the very parts the first
     one published;
   - the generated interfaces and the symbols table hold across parts for
     every form the code generator binds: inductive types and their
     accumulators, matches, fixpoints, cofixpoints;
   - a unit cut into one actual part, [<base>_p1], registers that part, so
     its definitions are linked to it and reused;
   - a worker's second unit, which refers to the worker's first published
     unit, is published too, and reused by another worker;
   - a part naming a name an earlier part does not export fails at
     compile time, and a failed compile leaves no slot.

   Every cast runs natively in a forked child, as a worker runs it, with
   the [native-conversion-failed] warning made an error: a cast that falls
   back to the VM fails, so a verdict always comes from native code. A
   child reports the module each definition of interest is linked to,
   which shows what it loaded from where. *)

open OUnit
open Utest
open Coq_checklib
open Names
open Constr

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let id = Id.of_string
let anon = Context.anonR
let lam s body = mkLambda (Context.make_annot (Name.Name (id s)) Sorts.Relevant, mkProp, body)
let rel = mkRel
let app f args = mkApp (f, args)
let cst c = UnsafeMonomorphic.mkConst c

(* Church booleans; a cast's conversion test does not type its sides. *)
let tt = lam "t" (lam "f" (rel 2))
let ff = lam "t" (lam "f" (rel 1))

let flags =
  let f = Declareops.safe_flags Conv_oracle.empty in
  { f with Declarations.enable_VM = true; enable_native_compiler = true }

let dp = DirPath.make [id "ConvCachePartsTest"]
let constant_of name = Constant.make2 (ModPath.MPfile dp) (id name)

(* A constant with its bytecode, as the checker holds one. *)
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
    const_type = mkProp;
    const_relevance = Sorts.Relevant;
    const_body_code = code;
    const_universes = Declarations.Monomorphic;
    const_inline_code = false;
    const_typing_flags = flags;
  } in
  Environ.add_constant c cb (Environ.set_vm_library vmtab env)

let empty_env () =
  let env = Environ.set_typing_flags flags Environ.empty_env in
  Environ.set_vm_library (Vmlibrary.set_path dp (Environ.vm_library env)) env

(* A chain [<name>1 … <name>12], link 1 negation and each link the
   previous one applied twice (so every link from 2 on is the identity on
   booleans), and a [user] naming the last link. Twelve constants, so a
   unit of the chain cuts into several parts. *)
let chain_env name =
  let link i = constant_of (Printf.sprintf "%s%d" name i) in
  let env = ref (add_constant (link 1) (lam "b" (app (rel 1) [| ff; tt |])) (empty_env ())) in
  for i = 2 to 12 do
    let prev = cst (link (i - 1)) in
    env := add_constant (link i) (lam "b" (app prev [| app prev [| rel 1 |] |])) !env
  done;
  let user = constant_of (name ^ "user") in
  env := add_constant user (lam "b" (app (cst (link 12)) [| rel 1 |])) !env;
  !env, user, link

let check_cast env t1 t2 =
  Typeops.check_cast env (Environ.make_judge mkProp t1) VMcast
    { Environ.utj_val = t2; utj_type = Sorts.prop }

(** {6 Running casts as a worker} *)

let temp_dir = Filename.concat (Filename.get_temp_dir_name ()) "convCacheParts_test"

type outcome = {
  verdicts : int list;     (* per cast: 0 accepted, 1 rejected, 2 any other failure *)
  prefixes : string list;  (* the module each constant is linked to, "-" if none *)
}

(* The casts [casts], in order, in one forked child; then the module each
   of [defs] is linked to in [env]. *)
let run env casts defs =
  let result = Filename.temp_file ~temp_dir "result" "" in
  match Unix.fork () with
  | 0 ->
    let codes = List.map (fun (t1, t2) ->
        match check_cast env t1 t2 with
        | () -> 0
        | exception Type_errors.TypeError _ -> 1
        | exception _ -> 2)
        casts
    in
    let ch = open_out result in
    output_string ch (String.concat " " (List.map string_of_int codes) ^ "\n");
    List.iter (fun d ->
        output_string ch
          (Option.default "-" (Nativecode.definition_prefix env (Nativecode.Dconst d)) ^ "\n"))
      defs;
    close_out ch;
    Unix._exit 0
  | pid ->
    (match snd (Unix.waitpid [] pid) with
     | Unix.WEXITED 0 -> ()
     | _ -> assert_failure "the worker child died");
    let ch = open_in result in
    let verdicts = List.map int_of_string (String.split_on_char ' ' (input_line ch)) in
    let prefixes = List.map (fun _ -> try input_line ch with End_of_file -> "?") defs in
    close_in ch;
    { verdicts; prefixes }

let pp_outcome o =
  Printf.sprintf "verdicts %s; linked to %s"
    (String.concat " " (List.map string_of_int o.verdicts)) (String.concat " " o.prefixes)

let ends_with s suffix =
  let n = String.length s and m = String.length suffix in
  n >= m && String.equal (String.sub s (n - m) m) suffix

(* The part number of a part prefix [<base>_p<k>.], if it is one. *)
let part_number p =
  match String.rindex_opt p '_' with
  | Some i when i + 2 < String.length p && p.[i + 1] = 'p' && ends_with p "." ->
    int_of_string_opt (String.sub p (i + 2) (String.length p - i - 3))
  | Some _ | None -> None

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
  CWarnings.set_flags "+native-conversion-failed";
  Nativecode.set_native_vm_conversion true;
  Nativelib.include_dirs := [kernel_cmi_dir ()];
  Nativelib.get_load_paths := (fun () -> []);
  Nativelib.force_temp_dir ();
  Typeops.set_native_conversion_after 0.;
  CheckWorkers.set_jobs ~profiling:false 4;
  ConvCache.enable ~jobs:4 ();
  CheckWorkers.set_jobs ~profiling:false 1

let with_parts n f =
  Nativelib.set_forced_parts n;
  Fun.protect ~finally:(fun () -> Nativelib.set_forced_parts None) f

let slot_files () =
  match !Nativelib.slots with
  | None -> []
  | Some (dir, _) ->
    List.filter (fun f -> String.length f > 5 && String.equal (String.sub f 0 5) "slot.")
      (Array.to_list (Sys.readdir dir))

(** {6 Verdicts and reuse} *)

let () = add_test "a unit in parts gives the verdicts of one module, natively, and is reused" (fun () ->
  assert_bool "the cache did not turn on" (ConvCache.is_enabled ());
  (* One module. *)
  with_parts (Some 1) (fun () ->
      let env, user, link = chain_env "whole" in
      let o = run env [app (cst user) [| tt |], tt; app (cst user) [| tt |], ff] [link 1; link 12] in
      assert_equal ~printer:pp_outcome ~msg:"one module: accepted, rejected, natively"
        { o with verdicts = [0; 1] } o;
      assert_bool "one module: a definition was linked to a part"
        (List.for_all (fun p -> Option.is_empty (part_number p)) o.prefixes));
  (* Three parts. *)
  with_parts (Some 3) (fun () ->
      let env, user, link = chain_env "parts" in
      let casts = [app (cst user) [| tt |], tt; app (cst user) [| tt |], ff] in
      let producer = run env casts [link 1; link 12] in
      assert_equal ~printer:pp_outcome ~msg:"three parts: accepted, rejected, natively"
        { producer with verdicts = [0; 1] } producer;
      (match List.map part_number producer.prefixes with
       | [Some 1; Some k] when k > 1 -> ()
       | _ -> assert_failure ("the unit was not cut into parts: " ^ pp_outcome producer));
      (* Another worker over the same declarations loads those parts. *)
      let consumer = run env casts [link 1; link 12] in
      assert_equal ~printer:pp_outcome ~msg:"the consumer gives the same verdicts, from the same parts"
        producer consumer);
  assert_bool "a slot was left behind" (CList.is_empty (slot_files ())))

(** {6 Generated forms across parts} *)

(* A library of inductive types, matches, fixpoints and a cofixpoint,
   type-checked by [Safe_typing]. *)
let senv =
  let s = Safe_typing.set_native_compiler true Safe_typing.empty_environment in
  let _, s = Safe_typing.start_library (DirPath.make [id "ConvCachePartsForms"]) s in
  ref s

let add_mind ?(finite = Declarations.Finite) name ctors =
  let entry = {
    Entries.mind_entry_record = None;
    mind_entry_finite = finite;
    mind_entry_params = [];
    mind_entry_inds = [{
        Entries.mind_entry_typename = id name;
        mind_entry_arity = mkSet;
        mind_entry_consnames = List.map (fun (n, _) -> id n) ctors;
        mind_entry_lc = List.map snd ctors;
      }];
    mind_entry_universes = Entries.Monomorphic_ind_entry;
    mind_entry_variance = None;
    mind_entry_private = None;
  } in
  let (mind, _), s = Safe_typing.add_mind (id name) entry !senv in
  senv := s;
  (mind, 0)

let add_def name body =
  let entry = Entries.DefinitionEntry {
      Entries.definition_entry_body = body;
      definition_entry_secctx = None;
      definition_entry_type = None;
      definition_entry_universes = Entries.Monomorphic_entry;
      definition_entry_inline_code = false;
    } in
  let c, s = Safe_typing.add_constant (id name) entry !senv in
  senv := s;
  c

let arrow a b = mkProd (anon, a, b)
let lambda domain body = mkLambda (anon, domain, body)

let case_info ind arities =
  { ci_ind = ind; ci_npar = 0; ci_cstr_ndecls = arities; ci_cstr_nargs = Array.copy arities;
    ci_pp_info = { style = MatchStyle } }

let case ci result scrutinee branches =
  mkCase (ci, UVars.Instance.empty, [||], (([| anon |], result), Sorts.Relevant),
          NoInvert, scrutinee, branches)

let branch arity body = Array.make arity anon, body

let bool = add_mind "bool" ["true", mkRel 1; "false", mkRel 1]
let nat = add_mind "nat" ["O", mkRel 1; "S", arrow (mkRel 1) (mkRel 2)]
let bool_t = UnsafeMonomorphic.mkInd bool
let nat_t = UnsafeMonomorphic.mkInd nat
let stream = add_mind ~finite:Declarations.CoFinite "stream" ["Cons", arrow bool_t (arrow (mkRel 2) (mkRel 3))]
let stream_t = UnsafeMonomorphic.mkInd stream

let true_ = UnsafeMonomorphic.mkConstruct (bool, 1)
let false_ = UnsafeMonomorphic.mkConstruct (bool, 2)
let zero = UnsafeMonomorphic.mkConstruct (nat, 1)
let succ n = app (UnsafeMonomorphic.mkConstruct (nat, 2)) [| n |]
let cons = UnsafeMonomorphic.mkConstruct (stream, 1)
let rec numeral k = if k = 0 then zero else succ (numeral (k - 1))

(* negb b := match b with true => false | false => true end *)
let negb = add_def "negb"
    (lambda bool_t (case (case_info bool [| 0; 0 |]) bool_t (rel 1)
                      [| branch 0 false_; branch 0 true_ |]))

(* even := fix even n := match n with O => true | S p => negb (even p) end *)
let even = add_def "even"
    (mkFix (([| 0 |], 0), ([| anon |], [| arrow nat_t bool_t |],
      [| lambda nat_t (case (case_info nat [| 0; 1 |]) bool_t (rel 1)
                         [| branch 0 true_;
                            branch 1 (app (cst negb) [| app (rel 3) [| rel 1 |] |]) |]) |])))

(* alt := cofix alt b := Cons b (alt (negb b)) *)
let alt = add_def "alt"
    (mkCoFix (0, ([| anon |], [| arrow bool_t stream_t |],
      [| lambda bool_t (app cons [| rel 1; app (rel 2) [| app (cst negb) [| rel 1 |] |] |]) |])))

(* nth := fix nth n s := match s with Cons x t => match n with O => x | S p => nth p t end end *)
let nth = add_def "nth"
    (mkFix (([| 0 |], 0), ([| anon |], [| arrow nat_t (arrow stream_t bool_t) |],
      [| lambda nat_t (lambda stream_t
           (case (case_info stream [| 2 |]) bool_t (rel 1)
              [| branch 2 (case (case_info nat [| 0; 1 |]) bool_t (rel 4)
                             [| branch 0 (rel 2);
                                branch 1 (app (rel 6) [| rel 1; rel 2 |]) |]) |])) |])))

let () = add_test "matches, fixpoints, a cofixpoint and inductives hold across parts" (fun () ->
  let env = Safe_typing.env_of_safe_env !senv in
  (* nth 5 (alt true) is false, and so is even 5; even 4 is true. *)
  let lhs = app (cst nth) [| numeral 5; app (cst alt) [| true_ |] |] in
  let casts = [lhs, app (cst even) [| numeral 5 |]; lhs, app (cst even) [| numeral 4 |]] in
  let defs = [negb; even; alt; nth] in
  with_parts (Some 4) (fun () ->
      let producer = run env casts defs in
      assert_equal ~printer:pp_outcome ~msg:"in parts: accepted, rejected, natively"
        { producer with verdicts = [0; 1] } producer;
      let parts = List.sort_uniq Int.compare (List.filter_map part_number producer.prefixes) in
      assert_bool ("the definitions were not spread over parts: " ^ pp_outcome producer)
        (List.length parts >= 2);
      let consumer = run env casts defs in
      assert_equal ~printer:pp_outcome ~msg:"the consumer gives the same verdicts, from the same parts"
        producer consumer))

(** {6 One actual part} *)

let () = add_test "a unit cut into one actual part registers that part" (fun () ->
  with_parts (Some 3) (fun () ->
      let single = constant_of "single" in
      let env = add_constant single (lam "b" (app (rel 1) [| ff; tt |])) (empty_env ()) in
      let casts = [app (cst single) [| tt |], ff] in
      let producer = run env casts [single] in
      assert_equal ~printer:pp_outcome ~msg:"accepted, natively" { producer with verdicts = [0] } producer;
      (match part_number (List.hd producer.prefixes) with
       | Some 1 -> ()
       | _ -> assert_failure ("single is not linked to the part <base>_p1: " ^ pp_outcome producer));
      let consumer = run env casts [single] in
      assert_equal ~printer:pp_outcome ~msg:"the consumer reuses that part" producer consumer))

(** {6 A worker's second unit} *)

let () = add_test "a unit that refers to the worker's own published unit is published" (fun () ->
  (* [a] is negation and [b x := a (a x)]. The worker decides [a tt] first,
     which publishes a unit for [a], then [b tt], whose unit holds [b]
     only and refers to the first one. *)
  let a = constant_of "ordera" and b = constant_of "orderb" in
  let env = add_constant a (lam "x" (app (rel 1) [| ff; tt |])) (empty_env ()) in
  let env = add_constant b (lam "x" (app (cst a) [| app (cst a) [| rel 1 |] |])) env in
  let producer = run env [app (cst a) [| tt |], ff; app (cst b) [| tt |], tt] [a; b] in
  assert_equal ~printer:pp_outcome ~msg:"both accepted, natively" { producer with verdicts = [0; 0] } producer;
  (match producer.prefixes with
   | [pa; pb] when not (String.equal pa pb) -> ()
   | _ -> assert_failure ("a and b are not in two units: " ^ pp_outcome producer));
  let consumer = run env [app (cst b) [| tt |], tt] [a; b] in
  assert_equal ~printer:pp_outcome ~msg:"another worker reuses both units"
    { verdicts = [0]; prefixes = producer.prefixes } consumer)

(** {6 Interfaces and failed compiles} *)

let compile_parts base files =
  Nativelib.compile_part_files ~base:(Filename.concat temp_dir base) files

let header = "open Nativevalues\n"

let () = add_test "a part naming a name an earlier part does not export fails at compile time" (fun () ->
  let p1_mli = "val exported : int\n" in
  let p1_ml = header ^ "let exported = 1\nlet hidden = 2\n" in
  let p2_mli = "val user : int\n" in
  let p2_ml = header ^ "open Crossref_p1\nlet user = exported + hidden\n" in
  let failed =
    match compile_parts "Crossref" [| p1_mli, p1_ml; p2_mli, p2_ml |] with
    | _ -> false
    | exception CErrors.UserError _ -> true
  in
  assert_bool "the reference to a name the part does not export compiled" failed;
  assert_bool "a .cmxs was linked" (not (Sys.file_exists (Filename.concat temp_dir "Crossref.cmxs")));
  (* The same parts, with the name exported, compile. *)
  let cmxs = compile_parts "Crossok"
      [| "val exported : int\nval hidden : int\n", p1_ml;
         p2_mli, header ^ "open Crossok_p1\nlet user = exported + hidden\n" |] in
  assert_bool "the parts with the name exported did not link" (Sys.file_exists cmxs);
  (* A part that does not parse: the compile fails and leaves no slot. *)
  (match compile_parts "Slotfail" [| "val x : int\n", header ^ "let x = (\n" |] with
   | _ -> assert_failure "a part that does not parse compiled"
   | exception CErrors.UserError _ -> ());
  assert_bool "a slot was left behind" (CList.is_empty (slot_files ()));
  assert_bool "this process still holds a slot" (CList.is_empty !Nativelib.held_slots))

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
