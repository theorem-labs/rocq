open Utest

let log_out_ch = open_log_out_ch __FILE__

(* The three examples of FIPS 180-4, appendix B ("abc", the 448-bit message
   and a million times 'a'), the empty string, the lengths around the two
   block boundaries of the padding, and a file read in more than one buffer.
   Every digest below was taken from an implementation that is not this one
   (Python's hashlib, which agrees with coreutils sha256sum), so a fault
   shared by this module's string and file paths cannot make a test pass. *)

let digest name description expected input =
  mk_eq_test name description expected (Sha256.string input)

let empty = digest "clib-sha256-empty"
    "the digest of the empty string"
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    ""

let abc = digest "clib-sha256-abc"
    "the digest of \"abc\" (FIPS 180-4, B.1)"
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    "abc"

let two_blocks = digest "clib-sha256-two-blocks"
    "the digest of the 448-bit message (FIPS 180-4, B.2)"
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

let million = digest "clib-sha256-million"
    "the digest of a million times 'a' (FIPS 180-4, B.3)"
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    (String.make 1000000 'a')

(* The padding is one 0x80 byte, then zeroes, then the length in eight bytes.
   At 55 bytes it ends the block exactly; at 56 and at every length up to 63
   the length needs a block of its own; at 64 the message ends a block and the
   padding fills the next one. 119 and 120 are the same three cases one block
   further on: 119 pads to the end of its second block, 120 needs a third. *)

let boundary (n, expected) =
  digest (Printf.sprintf "clib-sha256-boundary-%d" n)
    (Printf.sprintf "the digest of %d times 'a'" n)
    expected
    (String.make n 'a')

let boundaries = List.map boundary [
    55, "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318";
    56, "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a";
    63, "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34";
    64, "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb";
    119, "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb";
    120, "2f3d335432c70b580af0e8e1b3674a7c020d683aa5f73aaaedfdc55af904c21c";
  ]

let file_digest =
  let name = Filename.temp_file "sha256_tests" ".bin" in
  let got =
    Fun.protect ~finally:(fun () -> try Sys.remove name with Sys_error _ -> ())
      (fun () ->
         let ch = open_out_bin name in
         (* More than one read of the 65536-byte buffer, and a last read that
            does not end on a block boundary. *)
         Fun.protect ~finally:(fun () -> close_out ch)
           (fun () -> output_string ch (String.make 100000 'x'));
         Sha256.file name)
  in
  mk_eq_test "clib-sha256-file"
    "the digest of a file of 100000 times 'x'"
    "d69e68988157833272305aaf21f453c800346e8a3640db6578e260215542e5d4"
    got

let tests = [ empty; abc; two_blocks; million ] @ boundaries @ [ file_digest ]

let _ = run_tests __FILE__ log_out_ch tests
