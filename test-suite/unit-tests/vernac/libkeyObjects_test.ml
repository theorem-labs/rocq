open OUnit
open Utest
open Names

(* Unit tests of LibkeyObjects: the location-free label of a library, which
   coqc stores as the digest of its library segment (design D18). *)

let tests = ref []
let add_test name f = tests := mk_test name (TestCase f) :: !tests

let hex s =
  String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))

(* Toy object kinds, one per interface-key view. *)

let in_as_is : int * string -> Libobject.obj =
  Libobject.declare_object
    { (Libobject.default_object "LIBKEY-TEST-AS-IS") with
      Libobject.classify_function = (fun _ -> Libobject.Keep);
      interface_key = Libobject.Key_as_is }

let in_lident : lident -> Libobject.obj =
  Libobject.declare_object
    { (Libobject.default_object "LIBKEY-TEST-LIDENT") with
      Libobject.classify_function = (fun _ -> Libobject.Keep);
      interface_key = Libobject.Key_stripped (LocStrip.cast (fun id -> id)) }

let in_unknown : int -> Libobject.obj =
  Libobject.declare_object
    { (Libobject.default_object "LIBKEY-TEST-UNKNOWN") with
      Libobject.classify_function = (fun _ -> Libobject.Keep) }

let in_failing : int -> Libobject.obj =
  Libobject.declare_object
    { (Libobject.default_object "LIBKEY-TEST-FAILING") with
      Libobject.classify_function = (fun _ -> Libobject.Keep);
      interface_key = Libobject.Key_stripped (fun _ -> LocStrip.unknown "test value") }

let file = Loc.InFile { dirpath = None; file = "/tmp/A.v" }
let at line bp ep = Loc.create file line 0 bp ep

let lid ?loc s = CAst.make ?loc (Id.of_string s)

let atomic o = Libobject.AtomicObject o

let segment ?(keep = []) objs : Declaremods.library_objects =
  (objs, { Libobject.keep_objects = keep }, { Libobject.escape_objects = [] })

(* The fixed input of the test vector: a module holding a located name and
   an object without location, a kept object, and an empty syntax segment. *)
let vector_input loc_a loc_b =
  let module_ =
    Libobject.ModuleObject
      (Id.of_string "M", ([], Libobject.Objs [atomic (in_lident (lid ?loc:loc_a "x"))]))
  in
  let objs = segment ~keep:[atomic (in_lident (lid ?loc:loc_b "y"))]
      [module_; atomic (in_as_is (42, "forty-two"))]
  in
  (segment [], objs)

let dp s = DirPath.make (List.rev_map Id.of_string (String.split_on_char '.' s))

(* The compiled form of an empty library [name]. *)
let compiled name =
  let _, senv = Safe_typing.start_library (dp name) Safe_typing.empty_environment in
  let _, lib, _, _ = Safe_typing.export ~output_native_objects:false senv (dp name) in
  lib

let lib_a = compiled "LibkeyTest.A"

(* A summary: the library's name, its direct dependencies in order with
   their digests, the ones it only safe-required, and its attributes. *)
let summary ?(name = "LibkeyTest.A") ?(deps = []) ?(safe = []) ?(info = UserWarn.empty) ()
  : LibkeyObjects.summary =
  { LibkeyObjects.name = dp name;
    deps = Array.of_list (List.map (fun (n, d) -> (dp n, Safe_typing.Dvo_or_vi d)) deps);
    safe_deps = List.fold_left (fun s n -> DirPath.Set.add (dp n) s) DirPath.Set.empty safe;
    info }

let info ?since ?note ?(warns = []) () =
  { UserWarn.depr =
      (if Option.has_some since || Option.has_some note then Some (Deprecation.make ?since ?note ())
       else None);
    warn = List.map (fun (note, cats) -> UserWarn.make_warn ~note ~cats ()) warns }

let deps_a = [ "Corelib.Init.Prelude", String.make 16 'p'; "LibkeyTest.X", String.make 16 'x' ]

(* The summary of the test vector: two dependencies, the second
   safe-required, a deprecation and a warning. *)
let sum_a =
  summary ~deps:deps_a ~safe:["LibkeyTest.X"]
    ~info:(info ~since:"9.2" ~note:"old" ~warns:["careful", "label-test"] ()) ()

let objects_exn ?(compiled = lib_a) ?(summary = sum_a) (syntax, objects) =
  match LibkeyObjects.label_result ~summary ~compiled ~syntax ~objects with
  | Ok b -> b
  | Error what -> failwith ("no label: " ^ what)

(* Version 3 test vector: the label of [vector_input] over [lib_a] and
   [sum_a], without [Libkey]'s header, which holds the OCaml version and so
   differs between switches. It pins the layout of LibkeyObjects (version,
   the blinded compiled form, the segments' tree, the summary's view) and the
   encoding beneath it; a change of either must bump a version and change
   this value. [lib_a] is an empty library, so the axiom-or-opaque blinding
   ([blind_compiled]) is the identity on it. *)
let vector = "dd34e13f8c5a0d988f276832564586c6cb919849b5719fa7f9c9937849a7ffe2"

let () = add_test "layout version 3" (fun () ->
    assert_equal ~printer:string_of_int 3 LibkeyObjects.version)

(* The summary as the layout reads it, written out: the name, the
   dependencies as a list in their order, the safe dependencies in
   [DirPath.compare] order, and the attributes as strings. *)
let summary_view (s : LibkeyObjects.summary) =
  (s.name, Array.to_list s.deps, List.sort DirPath.compare (DirPath.Set.elements s.safe_deps),
   (Option.map (fun { Deprecation.since; note } -> (since, note)) s.info.UserWarn.depr,
    List.map (fun (w : UserWarn.warn) -> (w.note, w.cats)) s.info.UserWarn.warn))

let () = add_test "test vector" (fun () ->
    let label = objects_exn (vector_input (Some (at 3 10 11)) (Some (at 7 40 41))) in
    assert_equal ~msg:"32 bytes" ~printer:string_of_int 32 (String.length label);
    let syn, obj = vector_input None None in
    let headerless =
      Libkey.sha256 (Libkey.encode (Obj.repr
        (LibkeyObjects.version, LibkeyObjects.blind_compiled lib_a, syn, obj, summary_view sum_a))) in
    assert_equal ~msg:"label without the header" ~printer:(fun s -> s) vector (hex headerless))

(* The reference reading of the layout: Libkey.label of the version, the
   compiled form, the two segments as they would be with no location in
   them, and the summary's view. Independent of the pinned value above. *)
let () = add_test "layout" (fun () ->
    let label = objects_exn (vector_input (Some (at 3 10 11)) (Some (at 7 40 41))) in
    let syn, obj = vector_input None None in
    assert_equal ~printer:hex
      (Libkey.label (Obj.repr
        (LibkeyObjects.version, LibkeyObjects.blind_compiled lib_a, syn, obj, summary_view sum_a))) label)

let () = add_test "the compiled form counts" (fun () ->
    let input = vector_input None None in
    assert_bool "another library name"
      (not (String.equal (objects_exn input)
              (objects_exn ~compiled:(compiled "LibkeyTest.B") input))))

let () = add_test "locations do not count" (fun () ->
    let a = objects_exn (vector_input (Some (at 3 10 11)) (Some (at 7 40 41))) in
    let b = objects_exn (vector_input (Some (at 9 200 201)) None) in
    let c = objects_exn (vector_input None (Some (Loc.make_loc (0, 1)))) in
    assert_equal ~printer:hex a b;
    assert_equal ~printer:hex a c)

let differs msg x y =
  assert_bool msg (not (String.equal (objects_exn x) (objects_exn y)))

let () = add_test "every other field counts" (fun () ->
    let base = vector_input (Some (at 3 10 11)) None in
    let with_objs objs = (segment [], segment objs) in
    differs "identifier"
      (with_objs [atomic (in_lident (lid "x"))]) (with_objs [atomic (in_lident (lid "z"))]);
    differs "as-is payload"
      (with_objs [atomic (in_as_is (42, "a"))]) (with_objs [atomic (in_as_is (43, "a"))]);
    differs "as-is string"
      (with_objs [atomic (in_as_is (42, "a"))]) (with_objs [atomic (in_as_is (42, "b"))]);
    differs "object order"
      (with_objs [atomic (in_as_is (1, "a")); atomic (in_as_is (2, "a"))])
      (with_objs [atomic (in_as_is (2, "a")); atomic (in_as_is (1, "a"))]);
    differs "kind" (with_objs [atomic (in_as_is (1, "x"))])
      (with_objs [atomic (in_lident (lid "x"))]);
    differs "segment" base (snd base, fst base);
    differs "kept versus own"
      (segment [], segment [atomic (in_as_is (1, "a"))])
      (segment [], segment ~keep:[atomic (in_as_is (1, "a"))] []);
    differs "module name"
      (with_objs [Libobject.ModuleObject (Id.of_string "M", ([], Libobject.Objs []))])
      (with_objs [Libobject.ModuleObject (Id.of_string "N", ([], Libobject.Objs []))]))

(* Each field of the summary counts (Astra review, section 3.1: the safe/full
   modes of the dependencies change what a dependent's compile does). *)
let () = add_test "every field of the summary counts" (fun () ->
    let input = vector_input None None in
    let summary_differs msg s1 s2 =
      assert_bool msg (not (String.equal (objects_exn ~summary:s1 input) (objects_exn ~summary:s2 input))) in
    summary_differs "a dependency safe-required (Require (safe)) instead of required"
      (summary ~deps:deps_a ()) (summary ~deps:deps_a ~safe:["LibkeyTest.X"] ());
    summary_differs "which dependency is safe-required"
      (summary ~deps:deps_a ~safe:["LibkeyTest.X"] ())
      (summary ~deps:deps_a ~safe:["Corelib.Init.Prelude"] ());
    summary_differs "a dependency's digest"
      (summary ~deps:deps_a ())
      (summary ~deps:[ "Corelib.Init.Prelude", String.make 16 'p'; "LibkeyTest.X", String.make 16 'y' ] ());
    summary_differs "the order of the dependencies"
      (summary ~deps:deps_a ()) (summary ~deps:(List.rev deps_a) ());
    summary_differs "one more dependency"
      (summary ~deps:deps_a ()) (summary ~deps:(deps_a @ [ "LibkeyTest.Y", String.make 16 'y' ]) ());
    summary_differs "the library's name"
      (summary ~name:"LibkeyTest.A" ()) (summary ~name:"LibkeyTest.A2" ());
    summary_differs "a deprecation" (summary ()) (summary ~info:(info ~since:"9.2" ()) ());
    summary_differs "a deprecation's version"
      (summary ~info:(info ~since:"9.2" ()) ()) (summary ~info:(info ~since:"9.3" ()) ());
    summary_differs "a deprecation's note"
      (summary ~info:(info ~note:"a" ()) ()) (summary ~info:(info ~note:"b" ()) ());
    summary_differs "a deprecation's version against its note"
      (summary ~info:(info ~since:"a" ()) ()) (summary ~info:(info ~note:"a" ()) ());
    summary_differs "a warning" (summary ()) (summary ~info:(info ~warns:["n", "c"] ()) ());
    summary_differs "a warning's note"
      (summary ~info:(info ~warns:["n", "c"] ()) ()) (summary ~info:(info ~warns:["m", "c"] ()) ());
    summary_differs "a warning's categories"
      (summary ~info:(info ~warns:["n", "c"] ()) ()) (summary ~info:(info ~warns:["n", "d"] ()) ()))

(* The safe dependencies are a set: the shape of the balanced tree that holds
   it depends on the order of insertion, and must not count. *)
let () = add_test "the safe dependencies are read as a set" (fun () ->
    let names = List.init 9 (fun i -> Printf.sprintf "LibkeyTest.S%d" i) in
    let deps = List.map (fun n -> (n, String.make 16 's')) names in
    let input = vector_input None None in
    let a = objects_exn ~summary:(summary ~deps ~safe:names ()) input in
    let b = objects_exn ~summary:(summary ~deps ~safe:(List.rev names) ()) input in
    let c = objects_exn ~summary:(summary ~deps
                                    ~safe:(List.filteri (fun i _ -> i mod 2 = 0) names
                                           @ List.filteri (fun i _ -> i mod 2 = 1) names) ()) input in
    assert_equal ~printer:hex a b;
    assert_equal ~printer:hex a c)

let () = add_test "sharing does not count" (fun () ->
    let s = String.make 100 'a' in
    let shared = (segment [], segment [atomic (in_as_is (1, s)); atomic (in_as_is (1, s))]) in
    let copied = (segment [], segment [atomic (in_as_is (1, s));
                                       atomic (in_as_is (1, String.init 100 (fun _ -> 'a')))]) in
    assert_equal ~printer:hex (objects_exn shared) (objects_exn copied))

let () = add_test "stored objects keep their locations" (fun () ->
    let l = lid ~loc:(at 3 10 11) "x" in
    let _ = objects_exn (segment [], segment [atomic (in_lident l)]) in
    assert_bool "location kept" (Option.has_some l.CAst.loc))

let no_key msg expected (syntax, objects) =
  assert_equal ~msg ~printer:(fun x -> x) "None"
    (match LibkeyObjects.label ~summary:sum_a ~compiled:lib_a ~syntax ~objects with
     | None -> "None" | Some _ -> "Some");
  match LibkeyObjects.label_result ~summary:sum_a ~compiled:lib_a ~syntax ~objects with
  | Ok _ -> assert_failure msg
  | Error what -> assert_equal ~msg ~printer:(fun x -> x) expected what

let () = add_test "unknown kind: no key" (fun () ->
    no_key "unknown kind" "object segment: object kind LIBKEY-TEST-UNKNOWN"
      (segment [], segment [atomic (in_as_is (1, "a")); atomic (in_unknown 3)]);
    no_key "unknown kind inside a module" "syntax segment: object kind LIBKEY-TEST-UNKNOWN"
      (segment [Libobject.ModuleObject (Id.of_string "M", ([], Libobject.Objs [atomic (in_unknown 3)]))],
       segment []))

let () = add_test "stripper meets an unknown value: no key" (fun () ->
    no_key "failing stripper" "object segment: object kind LIBKEY-TEST-FAILING: test value"
      (segment [], segment [atomic (in_failing 0)]))

let wit_unregistered : (int, int, int) Genarg.genarg_type = Genarg.make0 "libkey-test-unregistered"

let () = add_test "unregistered generic argument: Unknown" (fun () ->
    let arg = Genarg.in_gen (Genarg.glbwit wit_unregistered) 0 in
    match Genstrip.generic_strip arg with
    | _ -> assert_failure "an unregistered generic argument was stripped"
    | exception LocStrip.Unknown what ->
      assert_equal ~printer:(fun x -> x) "generic argument libkey-test-unregistered" what)

let wit_registered : (lident, lident, lident) Genarg.genarg_type = Genarg.make0 "libkey-test-registered"
let () = Genstrip.register_strip0 wit_registered (LocStrip.cast (fun id -> id))

let () = add_test "registered generic argument, in a list" (fun () ->
    let strip l =
      Genarg.out_gen (Genarg.glbwit (Genarg.ListArg wit_registered))
        (Genstrip.generic_strip (Genarg.in_gen (Genarg.glbwit (Genarg.ListArg wit_registered)) l)) in
    let l = strip [lid ~loc:(at 1 0 1) "a"; lid "b"] in
    assert_bool "locations stripped" (List.for_all (fun x -> Option.is_empty x.CAst.loc) l);
    assert_equal ~printer:(fun x -> x) "a b"
      (String.concat " " (List.map (fun x -> Id.to_string x.CAst.v) l)))

(* The axiom-or-opaque-proof blinding (S1b): [Undef None] (an axiom) and
   [OpaqueDef _] (an opaque proof) collapse to the canonical [Undef None], so
   [Admitted <-> Qed] does not change the label; [Def] (a transparent body
   conversion unfolds) and [Undef (Some _)] (an inlinable parameter) stay
   distinct. Every other field is kept, which the fixture and the mutation
   sweep exercise on real compiled forms. *)
let () = add_test "blind_constant collapses axiom and opaque proof, keeps Def and inline" (fun () ->
    let opaque, _ = Opaqueproof.create (dp "LibkeyTest.A") Opaqueproof.empty_opaquetab in
    let base : Declarations.constant_body =
      { Declarations.const_hyps = [];
        const_univ_hyps = UVars.Instance.empty;
        const_body = Declarations.Undef None;
        const_type = Constr.mkRel 1;
        const_relevance = Sorts.Relevant;
        const_body_code = None;
        const_universes = Declarations.Monomorphic;
        const_inline_code = false;
        const_typing_flags = Environ.typing_flags Environ.empty_env } in
    let is_undef_none cb = match cb.Declarations.const_body with
      | Declarations.Undef None -> true | _ -> false in
    assert_bool "OpaqueDef collapses to Undef None"
      (is_undef_none (LibkeyObjects.blind_constant { base with Declarations.const_body = Declarations.OpaqueDef opaque }));
    assert_bool "Undef None stays Undef None"
      (is_undef_none (LibkeyObjects.blind_constant base));
    assert_bool "a transparent body is not blinded"
      (match (LibkeyObjects.blind_constant
                { base with Declarations.const_body = Declarations.Def (Constr.mkRel 1) }).Declarations.const_body with
       | Declarations.Def _ -> true | _ -> false);
    assert_bool "an inlinable parameter is not blinded"
      (match (LibkeyObjects.blind_constant
                { base with Declarations.const_body = Declarations.Undef (Some 1) }).Declarations.const_body with
       | Declarations.Undef (Some 1) -> true | _ -> false))


let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
