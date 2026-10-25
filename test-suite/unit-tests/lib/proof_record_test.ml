open Utest

let log_out_ch = open_log_out_ch __FILE__

module R = Proof_record

let toolchain : R.toolchain = R.{
  binary = "0123456789abcdef0123456789abcdef";
  plugins = [ ("rocq-runtime.plugins.ltac", "00112233445566778899aabbccddeeff") ];
  load_order = [ ("Corelib.Init.Prelude", "ffeeddccbbaa99887766554433221100") ];
  warnings = "-notation-incompatible-prefix";
  safe_deps = [ "Corelib.Init.Logic" ];
  stack_limit = "8388608";
}

let header : R.header = R.{
  version = R.format_version;
  library = "Top.File";
  source = "dir/File.v";
  source_digest = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
  toolchain;
  memory_cap = "unlimited";
  rlimit_as = "unlimited";
  rlimit_data = "unlimited";
  overcommit_memory = "0";
  skip_qed_typecheck = true;
  tables_at_start = true;
}

let proof : R.proof = R.{
  name = "Top.File.lemma \"quoted\"\n\xc3\xa9";
  statement = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
  sentences = "cccccccccccccccccccccccccccccccc";
  closer = "Qed";
  toolchain_key = R.toolchain_key toolchain;
  position = { module_path = "Top.File.M"; section_path = "Top.File.M.S" };
  ineligible = [ { reason = "catchall"; detail = "pretyping/evarconv.ml:285" } ];
  reads = [
    { row = "1"; channel = "constant"; key = "Top.File.foo"; value = Some "dddddddddddddddddddddddddddddddd" };
    { row = "6"; channel = "xref"; key = "bar"; value = None };
    { row = "7"; channel = "hint_db"; key = "core"; value = Some "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee" };
  ];
  start_tables = [
    { row = "8"; channel = "typeclass_table"; key = "instances"; value = Some "99999999999999999999999999999999" };
  ];
  writes = {
    universe_levels = [ "Top.File.12"; "Top.File.13" ];
    counters = [ ("evar", 4); ("univ", 2) ];
    constraints = [ "Top.File.12 < Top.File.13" ];
    schemes = [ "Top.File.t_rect" ];
    constraint_sources = [ "Top.File.lemma" ];
    warnings_raised = [ ("deprecated-reference", "Reference foo is deprecated.") ];
  };
  kernel_check = false;
  wall_s = 1.5;
  cpu_s = 0.1;
}

let trailer : R.trailer = R.{ file_wall_s = 12.25; file_cpu_s = 11.; peak_rss_kb = 123456; proof_count = 1 }

let file : R.file = R.{ header; proofs = [ proof ]; trailer }

let written () =
  let buf = Buffer.create 1024 in
  R.output_header buf header;
  R.output_proof buf proof;
  buf

let roundtrip =
  let buf = written () in
  R.output_trailer buf trailer;
  let text = Buffer.contents buf in
  let lines = String.split_on_char '\n' text in
  mk_bool_test "proof-record-roundtrip"
    "a written record reads back equal, one JSON object per line"
    (R.parse_string text = file
     && List.length lines = 4
     && List.nth lines 3 = ""
     && List.for_all (fun l -> l = "" || (l.[0] = '{' && l.[String.length l - 1] = '}')) lines)

let refused text =
  match R.parse_string text with
  | _ -> false
  | exception R.Parse_error _ -> true

let bad_input =
  let buf = Buffer.create 256 in
  R.output_header buf { header with version = R.format_version + 1 };
  let other_version = Buffer.contents buf in
  let good = Buffer.contents (written ()) in
  let header_line = List.hd (String.split_on_char '\n' good) in
  let trailer_line n =
    Printf.sprintf
      "{\"kind\":\"trailer\",\"file_wall_s\":1,\"file_cpu_s\":1,\"peak_rss_kb\":1,\"proof_count\":%d}\n" n in
  mk_bool_test "proof-record-refused"
    "another format version, a missing header or trailer, an extra field, a wrong proof count and a line after the \
     trailer are refused"
    (not (refused (good ^ trailer_line 1))
     && refused other_version
     && refused ""
     && refused good
     && refused (good ^ trailer_line 2)
     && refused (String.concat "" [ String.sub header_line 0 (String.length header_line - 1); ",\"extra\":1}\n";
                                    String.concat "\n" (List.tl (String.split_on_char '\n' good)); trailer_line 1 ])
     && refused (good ^ trailer_line 1 ^ trailer_line 1))

let toolchain_key_fields =
  let k : R.toolchain_key = R.toolchain_key toolchain in
  let k' : R.toolchain_key = R.toolchain_key { toolchain with warnings = "+all" } in
  let k'' : R.toolchain_key = R.toolchain_key { toolchain with plugins = [] } in
  mk_bool_test "proof-record-toolchain-fields"
    "each key item 2 field is separate; changing one field changes only that field"
    (k.binary = toolchain.binary
     && k.stack_limit = toolchain.stack_limit
     && k.warnings = toolchain.warnings
     && k.warnings <> k'.warnings
     && k.plugins = k'.plugins && k.load_order = k'.load_order && k.safe_deps = k'.safe_deps
     && k.plugins <> k''.plugins && k.load_order = k''.load_order)

(* Structural digest *)

let mk_list () = List.init 3 (fun i -> i + 1)

let sharing =
  let shared = let x = mk_list () in (x, x) in
  let unshared = (mk_list (), mk_list ()) in
  mk_bool_test "proof-record-digest-sharing"
    "the digest does not depend on physical sharing"
    (R.digest_value shared = R.digest_value unshared
     && R.digest_value shared <> R.digest_value (mk_list (), List.init 3 (fun i -> i + 2)))

let kinds =
  mk_bool_test "proof-record-digest-kinds"
    "strings, floats, ints and constructors are told apart"
    (let d = R.digest_value in
     d "a" <> d "b" && d 1.0 <> d 2.0 && d (Some 0) <> d None && d [| 1.0 |] <> d [| 2.0 |]
     && d (Obj.repr 0) <> d (Obj.repr "") && d 1L <> d 2L && String.length (d "a") = 32)

let deep =
  mk_bool_test "proof-record-digest-deep"
    "a list of a million elements is digested without stack overflow"
    (String.length (R.digest_value (List.init 1_000_000 (fun i -> i))) = 32)

(* Locations of the compiled file are removed; a location of another source stays.
   The source values are built at run time so that they are not physically shared. *)
let src () = Loc.InFile { dirpath = Some (String.concat "" ["T"; "op"]); file = String.concat "" ["a"; ".v"] }
let other = Loc.InFile { dirpath = Some "Top"; file = "b.v" }
let loc1 = Loc.create (src ()) 1 0 0 10
let loc2 = Loc.create (src ()) 5 90 100 110
let loc3 = Loc.create other 1 0 0 10
let loc4 = Loc.create other 5 90 100 110

let locations =
  mk_bool_test "proof-record-digest-locations"
    "with ~locs, values that differ only in locations of that source have equal digests"
    (let mk l l' id = CAst.make ~loc:l (Names.Id.of_string id, [ CAst.make ~loc:l' "t" ]) in
     let d = R.digest_value ~locs:(src ()) in
     d (mk loc1 loc2 "x") = d (mk loc2 loc1 "x")
     && d (mk loc1 loc2 "x") <> d (mk loc1 loc2 "y")
     && d (mk loc1 loc3 "x") <> d (mk loc1 loc4 "x")
     && R.digest_value (mk loc1 loc2 "x") <> R.digest_value (mk loc2 loc1 "x"))

let unhashable =
  mk_bool_test "proof-record-digest-unhashable"
    "a closure, a cycle or an unforced lazy cannot be digested"
    (let rec cyc = 1 :: cyc in
     let f = Sys.opaque_identity (fun x -> x + 1) in
     let l = lazy (Sys.opaque_identity 1 + 1) in
     let fails v = match R.digest_value v with _ -> false | exception R.Unhashable _ -> true in
     fails (1, f) && fails cyc && fails l
     && (Lazy.force l = 2 && not (fails l)))

let vo_path =
  mk_bool_test "proof-record-path"
    "the record sits beside the .vo"
    (R.path_of_vo "dir/Foo.vo" = "dir/Foo.proof-record.jsonl"
     && R.path_of_vo "Foo.vo" = "Foo.proof-record.jsonl")

(* The memo of blocks lives from one call to the next, so a persistent value
   digested again after a change costs its delta. It must not change a digest:
   the same value digested with an empty memo and with a full one is the same,
   and a big value digested once and shared is the digest of its copy. *)
let memo =
  mk_bool_test "proof-record-digest-memo"
    "the memo kept between calls does not change a digest"
    (let big () = List.init 200 (fun i -> (i, string_of_int i)) in
     let a = big () in
     let first = R.digest_value a in
     R.reset_memo ();
     let again = R.digest_value a in
     let fresh = R.digest_value (big ()) in
     first = again && first = fresh
     && R.digest_value (a, a) = R.digest_value (a, big ())
     && R.digest_value (a, a) <> R.digest_value (a, List.tl (big ())))

(* The memo is hashed by the block's address. A block that the GC moves
   after it was memoized is then looked for in another bucket: the lookup
   misses and the block is walked again. That must cost time only. And a long
   run of look-alike blocks, which a bounded structural hash puts in one
   bucket, must cost time linear in its length (R1M1's profile of a
   registration file: 581 times its stock CPU, 95.6% in the bucket walk). *)
let memo_moves =
  mk_bool_test "proof-record-digest-memo-moves"
    "a block moved by the GC keeps its digest, and look-alike blocks are linear"
    (let image n = List.init n (fun _ -> (0, "\000")) in
     let a = image 50_000 in
     let before = R.digest_value a in
     Gc.compact ();
     let after = R.digest_value a in
     R.reset_memo ();
     let fresh = R.digest_value (image 50_000) in
     let t0 = Sys.time () in
     let _ = R.digest_value (image 400_000) in
     let t1 = Sys.time () in
     before = after && before = fresh && t1 -. t0 < 5.0)

let tests =
  [ roundtrip; bad_input; toolchain_key_fields; sharing; kinds; deep; locations; unhashable; memo;
    memo_moves; vo_path ]

let _ = run_tests __FILE__ log_out_ch tests
