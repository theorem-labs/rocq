(* The checker's description of the keepfacts segment (Values.v_keepfacts)
   against marshalled KeepFacts.t values: rocq-library-label validates every
   keepfacts segment it reads against it and reads one that does not match
   as absent (checker/library_label.ml, read_keep_facts). A well-shaped value
   passes; a value of another shape fails, so a KeepFacts.t changed without
   its description is caught when this build reads its own segments. *)

open OUnit
open Utest
open Coq_checklib

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let check v = Validate.check Values.v_keepfacts (Analyze.parse_string (Marshal.to_string v []))

let ok what v =
  match check v with
  | Ok () -> ()
  | Error why -> assert_failure (what ^ ": refused: " ^ why)

let refused what v =
  match check v with
  | Ok () -> assert_failure (what ^ ": accepted")
  | Error _ -> ()

let query = { KeepFacts.constant = "A.c"; library = Some "A"; opaque = true }

let full : KeepFacts.t = {
  KeepFacts.assumptions = Some [("A.l", ["axiom:A.ax"; "theory:impredicative_set"])];
  opacity_queries = [query; { query with KeepFacts.library = None; opaque = false }];
}

let () = add_test "a well-shaped value passes" (fun () ->
    ok "closures and queries" full;
    ok "no closures, no queries" { KeepFacts.assumptions = None; opacity_queries = [] };
    ok "empty closures" { KeepFacts.assumptions = Some []; opacity_queries = [query] })

let () = add_test "a value of another shape fails" (fun () ->
    refused "a pair of a string and an int" (Obj.repr ("A.c", 3));
    refused "an int where the opacity bool is"
      (Obj.repr { full with KeepFacts.opacity_queries = [Obj.magic ("A.c", Some "A", 5)] });
    refused "a query with a field missing"
      (Obj.repr { full with KeepFacts.opacity_queries = [Obj.magic ("A.c", Some "A")] });
    refused "an int where a closure's keys are"
      (Obj.repr { full with KeepFacts.assumptions = Some [Obj.magic ("A.l", 7)] });
    refused "a list where the closures' option is"
      (Obj.repr { full with KeepFacts.assumptions = Obj.magic [("A.l", ["axiom:A.ax"])] }))

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
