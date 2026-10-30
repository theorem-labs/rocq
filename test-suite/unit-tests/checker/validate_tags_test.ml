(* rocq-prover/rocq#22407: where a record, tuple or array is expected, the .vo
   value validator must admit exactly the tags of a non-constant constructor.
   The tuple, record and array validators bound no tag of their own, so
   val_block is the only test.

   Upstream's fix (rocq-prover/rocq#22408) ships no test; this guard is ours,
   and a later sync with upstream should keep it. *)

open OUnit
open Utest
open Coq_checklib

(* Is a two-field block of tag [tag] admitted against the shape
   Values.v_tuple "record" [| v_int; v_int |]? *)
let admitted tag =
  let mem = Analyze.(LargeArray.make 1 (Struct (tag, [| Int 0; Int 0 |]))) in
  let record = Values.(v_tuple "record" [| v_int; v_int |]) in
  match Validate.validate record (Analyze.Ptr 0, mem) with
  | () -> true
  | exception Failure _ -> false

let test () =
  for tag = 0 to 255 do
    let expected =
      Obj.first_non_constant_constructor_tag <= tag && tag <= Obj.last_non_constant_constructor_tag
    in
    if admitted tag <> expected then
      assert_failure (Printf.sprintf "tag %d: admitted = %b, expected %b" tag (not expected) expected)
  done

let () =
  run_tests __FILE__ (open_log_out_ch __FILE__)
    [ mk_test "val_block admits exactly the non-constant constructor tags" (TestCase test) ]
