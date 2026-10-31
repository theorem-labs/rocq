open Utest

let log_out_ch = open_log_out_ch __FILE__

(* The three example digests of FIPS 180-4, appendix B, plus a message long
   enough to need more than one block of padding and a file. *)

let empty = mk_eq_test "clib-sha256-empty"
    "the digest of the empty string"
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    (Sha256.string "")

let abc = mk_eq_test "clib-sha256-abc"
    "the digest of \"abc\""
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    (Sha256.string "abc")

let two_blocks = mk_eq_test "clib-sha256-two-blocks"
    "the digest of the 896-bit message"
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    (Sha256.string
       "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")

(* A message of 119 bytes: the padding takes the block past 64 bytes, so the
   length goes into a block of its own. *)
let padding = mk_eq_test "clib-sha256-padding"
    "the digest of 119 times 'a'"
    "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb"
    (Sha256.string (String.make 119 'a'))

let file_digest =
  let name = Filename.temp_file "sha256_tests" ".bin" in
  let ch = open_out_bin name in
  (* More than one read of the 65536-byte buffer. *)
  let block = String.make 1000 'x' in
  for _ = 1 to 100 do output_string ch block done;
  close_out ch;
  let got = Sha256.file name in
  Sys.remove name;
  mk_eq_test "clib-sha256-file"
    "the digest of a file of 100000 times 'x'"
    (Sha256.string (String.concat "" (List.init 100 (fun _ -> block))))
    got

let tests = [ empty; abc; two_blocks; padding; file_digest ]

let _ = run_tests __FILE__ log_out_ch tests
