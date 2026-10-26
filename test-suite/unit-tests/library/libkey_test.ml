(* Libkey: the canonical encoding of values and SHA-256 that the library
   label hashes (library/rocq_libkey.c). *)

open OUnit
open Utest

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let hex s =
  String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))

(* {6 SHA-256} *)

(* Reference digests from Python's hashlib. *)
let sha_vectors = [
  "", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
  "abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";
  String.make 55 'a', "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318";
  String.make 56 'a', "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a";
  String.make 63 'a', "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34";
  String.make 64 'a', "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb";
  String.make 119 'a', "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb";
  String.make 1000000 'a', "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0";
  String.concat "" (List.init 3 (fun _ -> String.init 256 Char.chr)),
  "f3a25aa93aa2fbba28d79260535bbd6a5eb0fc1c24a8b0f04e12b484c1dfe363";
]

let check_vectors which =
  List.iter (fun (msg, expected) ->
      assert_equal ~printer:(fun s -> s)
        ~msg:(Printf.sprintf "%s sha256 of %d bytes" which (String.length msg))
        expected (hex (Libkey.sha256 msg)))
    sha_vectors

let () = add_test "sha256 test vectors, fastest compression" (fun () -> check_vectors "fastest")

(* On Linux, the "fastest" vectors above ran the SHA extensions exactly when
   the processor reports them, so a SHA-NI machine checks that code. *)
let () = add_test "fastest compression is the SHA extensions where the CPU has them" (fun () ->
    match In_channel.with_open_text "/proc/cpuinfo" In_channel.input_all with
    | exception Sys_error _ -> ()
    | info ->
      let has_sha_ni =
        Sys.word_size = 64 &&
        List.exists (fun l ->
            String.length l > 5 && String.sub l 0 5 = "flags" &&
            List.mem "sha_ni" (String.split_on_char ' ' l))
          (String.split_on_char '\n' info)
      in
      assert_equal ~printer:string_of_bool ~msg:"SHA extensions selected" has_sha_ni
        (Libkey.sha256_extensions ()))

let () = add_test "sha256 test vectors, portable compression" (fun () ->
    Libkey.force_portable_sha256 true;
    Fun.protect ~finally:(fun () -> Libkey.force_portable_sha256 false)
      (fun () -> check_vectors "portable"))

(* {6 The documented byte layout, recomputed naively} *)

let uvar n =
  let b = Buffer.create 10 in
  let rec go n =
    if n < 0x80 && n >= 0 then Buffer.add_char b (Char.chr n)
    else begin Buffer.add_char b (Char.chr (n land 0x7f lor 0x80)); go (n lsr 7) end
  in
  go n; Buffer.contents b

let zigzag n = (n lsl 1) lxor (n asr (Sys.int_size - 1))

let f64 x =
  let b = Bytes.create 8 in
  Bytes.set_int64_le b 0 (Int64.bits_of_float x); Bytes.to_string b

let rec ref_repr (o : Obj.t) =
  let e = ref_enc o in
  if String.length e < 64 then e else "\007" ^ Libkey.sha256 e
and ref_enc (o : Obj.t) =
  if Obj.is_int o then "\000" ^ uvar (zigzag (Obj.obj o : int))
  else
    let tag = Obj.tag o in
    if tag = Obj.string_tag then
      let s : string = Obj.obj o in "\001" ^ uvar (String.length s) ^ s
    else if tag = Obj.double_tag then "\002" ^ f64 (Obj.obj o : float)
    else if tag = Obj.double_array_tag then
      let a : float array = Obj.obj o in
      "\003" ^ uvar (Array.length a) ^ String.concat "" (Array.to_list (Array.map f64 a))
    else begin
      assert (tag < Obj.lazy_tag);
      String.make 1 '\004' ^ String.make 1 (Char.chr tag) ^ uvar (Obj.size o)
      ^ String.concat "" (List.init (Obj.size o) (fun i -> ref_repr (Obj.field o i)))
    end

type record = { a : int; b : string; c : float; d : float array; e : record option }
type variant = A | B of int | C of string * variant | D of variant list

let samples : (string * Obj.t) list =
  let r = { a = 7; b = String.make 70 'r'; c = 0.5; d = [| 1.; 2. |]; e = None } in
  [ "zero", Obj.repr 0; "one", Obj.repr 1; "minus one", Obj.repr (-1);
    "63", Obj.repr 63; "64", Obj.repr 64; "-64", Obj.repr (-64); "-65", Obj.repr (-65);
    "max_int", Obj.repr max_int; "min_int", Obj.repr min_int;
    "empty string", Obj.repr ""; "short string", Obj.repr "abc";
    (* 1 + 1 + n bytes: 61 is inline, 62 is the first digest. *)
    "61 bytes", Obj.repr (String.make 61 'x'); "62 bytes", Obj.repr (String.make 62 'x');
    "long string", Obj.repr (String.make 1000 'y');
    "float", Obj.repr 3.25; "nan", Obj.repr Float.nan; "negative zero", Obj.repr (-0.);
    "empty float array", Obj.repr ([||] : float array);
    "7 floats", Obj.repr (Array.make 7 1.5); "8 floats", Obj.repr (Array.make 8 1.5);
    "record", Obj.repr r; "nested record", Obj.repr { r with e = Some r };
    "constant constructor", Obj.repr A; "variants", Obj.repr (D [A; B 3; C ("c", D []); B (-5)]);
    "list", Obj.repr (List.init 300 (fun i -> i * i));
    "tag 200", (let o = Obj.new_block 200 2 in Obj.set_field o 0 (Obj.repr 1);
                Obj.set_field o 1 (Obj.repr "two"); o);
    "empty block", Obj.repr [||];
  ]

let () = add_test "encoding follows the documented layout" (fun () ->
    List.iter (fun (name, v) ->
        assert_equal ~msg:name ~printer:String.escaped (ref_repr v) (Libkey.encode v))
      samples)

let () = add_test "label is the first 16 bytes of the header's and encoding's digest" (fun () ->
    let v = Obj.repr (List.init 50 string_of_int) in
    let ocaml = Coq_config.caml_version in
    let u32 n = let b = Bytes.create 4 in Bytes.set_int32_le b 0 (Int32.of_int n); Bytes.to_string b in
    let header = "rocq-library-label\000" ^ u32 Libkey.version
                 ^ u32 (Int32.to_int Coq_config.vo_version) ^ u32 Sys.word_size
                 ^ u32 (String.length ocaml) ^ ocaml in
    assert_equal ~printer:hex (String.sub (Libkey.sha256 (header ^ ref_repr v)) 0 16) (Libkey.label v))

let () = add_test "encoding ignores physical sharing" (fun () ->
    let big () = List.init 100 (fun i -> String.make 10 (Char.chr (65 + i mod 26))) in
    let x = big () in
    assert_equal ~printer:hex (Libkey.encode (Obj.repr (x, x))) (Libkey.encode (Obj.repr (x, big ())));
    (* A DAG whose tree is exponential: each level holds the one below twice. *)
    let rec dag n = if n = 0 then Obj.repr "leaf" else let d = dag (n - 1) in Obj.repr (d, d) in
    let rec tree n = if n = 0 then Obj.repr "leaf" else Obj.repr (tree (n - 1), tree (n - 1)) in
    assert_equal ~printer:hex (Libkey.encode (tree 12)) (Libkey.encode (dag 12));
    ignore (Libkey.encode (dag 200)))

let () = add_test "every field counts" (fun () ->
    let differ a b = assert_bool "differ" (Libkey.encode (Obj.repr a) <> Libkey.encode (Obj.repr b)) in
    differ (1, 2) (2, 1); differ [1; 2] [1; 2; 3]; differ (B 1) (C ("", A)); differ "a" "b";
    differ (Obj.repr 1) (Obj.repr "1"); differ (Obj.repr 1.) (Obj.repr [| 1. |]);
    (* A block of tag 0 against one of tag 1 with the same field. *)
    differ (Obj.repr (Some 1))
      (let o = Obj.new_block 1 1 in Obj.set_field o 0 (Obj.repr 1); o))

let () = add_test "a deep value does not overflow the stack" (fun () ->
    let rec chain n acc = if n = 0 then acc else chain (n - 1) (Obj.repr (n, acc)) in
    let e = Libkey.encode (chain 2_000_000 (Obj.repr 0)) in
    assert_bool "a repr is at most 65 bytes" (String.length e <= 65);
    assert_bool "the depth counts" (e <> Libkey.encode (chain 1_999_999 (Obj.repr 0))))

let () = add_test "values outside the layout are refused" (fun () ->
    let unsupported v = match Libkey.encode (Obj.repr v) with
      | _ -> false
      | exception Libkey.Unsupported _ -> true
    in
    assert_bool "custom block" (unsupported (1, Int64.of_int 5));
    assert_bool "closure" (unsupported (1, fun x -> x + 1));
    assert_bool "lazy value" (unsupported (1, lazy (print_string "")));
    assert_bool "object" (unsupported (1, object method m = 1 end));
    let rec cyc = 1 :: cyc in
    assert_bool "cycle" (unsupported cyc))

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
