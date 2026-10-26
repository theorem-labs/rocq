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

let objects_exn ?(compiled = lib_a) (syntax, objects) =
  match LibkeyObjects.label_result ~compiled ~syntax ~objects with
  | Ok b -> b
  | Error what -> failwith ("no label: " ^ what)

(* Version 1 test vector: the label of [vector_input] over [lib_a]. It pins
   the layout of LibkeyObjects (version, the compiled form, the segments'
   tree) and of Libkey beneath it; a change of either must bump a version
   and change this value. *)
let vector = "7e9786986851210918c771d2a27c324e"

let () = add_test "test vector" (fun () ->
    let label = objects_exn (vector_input (Some (at 3 10 11)) (Some (at 7 40 41))) in
    assert_equal ~msg:"16 bytes" ~printer:string_of_int 16 (String.length label);
    assert_equal ~msg:"label" ~printer:(fun s -> s) vector (hex label))

(* The reference reading of the layout: Libkey.label of the version, the
   compiled form and the two segments as they would be with no location in
   them. Independent of the pinned value above. *)
let () = add_test "layout" (fun () ->
    let label = objects_exn (vector_input (Some (at 3 10 11)) (Some (at 7 40 41))) in
    let syn, obj = vector_input None None in
    assert_equal ~printer:hex
      (Libkey.label (Obj.repr (LibkeyObjects.version, lib_a, syn, obj))) label)

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
    (match LibkeyObjects.label ~compiled:lib_a ~syntax ~objects with
     | None -> "None" | Some _ -> "Some");
  match LibkeyObjects.label_result ~compiled:lib_a ~syntax ~objects with
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

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
