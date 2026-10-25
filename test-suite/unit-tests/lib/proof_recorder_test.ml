open Utest

let log_out_ch = open_log_out_ch __FILE__

module R = Proof_record
module Rec = Proof_recorder

let reset () = Rec.stop ()

let toolchain : R.toolchain = R.{
  binary = "0123456789abcdef0123456789abcdef";
  plugins = [];
  load_order = [];
  warnings = "";
  safe_deps = [];
  stack_limit = "unlimited";
}

let start ?(tables = false) () =
  reset ();
  Rec.start ~library:"Top.File" ~source:"dir/File.v" ~source_digest:(String.make 32 'a')
    ~toolchain:(fun () -> toolchain) ~skip_qed_typecheck:false ~tables_at_start:tables

let open_proof ?(name = "Top.File.lemma") () =
  Rec.open_proof ~name ~statement:(fun () -> String.make 32 'b')
    ~position:R.{ module_path = "Top.File"; section_path = "" }

let close_proof ?(closer = "Qed") ?(kernel_check = true) () =
  Rec.close_proof ~closer ~kernel_check

let the_file () =
  let path = Filename.temp_file "proof-record" ".jsonl" in
  Rec.write path;
  let ic = open_in_bin path in
  let text = really_input_string ic (in_channel_length ic) in
  close_in ic;
  Sys.remove path;
  R.parse_string text

(* Off by default: every entry point is a no-op and nothing is written. *)
let inert =
  reset ();
  let before = Rec.active () in
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "Top.x") ~value:(fun () -> Some "d");
  Rec.ineligible ~reason:"catchall" ~detail:"f.ml:1";
  open_proof ();
  close_proof ();
  mk_bool_test "recorder-inert"
    "with no start, every call is a no-op and no proof is held"
    (not before && not (Rec.active ()) && Rec.current_name () = None)

let one_proof =
  start ();
  open_proof ();
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "Top.x") ~value:(fun () -> Some "d1");
  Rec.read ~row:"6" ~channel:"xref" ~key:(fun () -> "y") ~value:(fun () -> None);
  close_proof ();
  let f = the_file () in
  let p = List.hd f.R.proofs in
  mk_bool_test "recorder-one-proof"
    "a started and closed proof writes one entry with its reads, in order"
    (f.R.header.R.library = "Top.File"
     && f.R.trailer.R.proof_count = 1
     && List.length f.R.proofs = 1
     && p.R.name = "Top.File.lemma" && p.R.closer = "Qed" && p.R.kernel_check
     && p.R.ineligible = []
     && List.map (fun r -> (r.R.row, r.R.key, r.R.value)) p.R.reads
        = [ ("1", "Top.x", Some "d1"); ("6", "y", None) ]
     && p.R.wall_s >= 0. && p.R.cpu_s >= 0.)

(* Reads outside a proof, and reads during the kernel check, are dropped. *)
let outside =
  start ();
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "before") ~value:(fun () -> Some "d");
  open_proof ();
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "inside") ~value:(fun () -> Some "d");
  let during = Rec.without_recording (fun () ->
      Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "kernel") ~value:(fun () -> Some "d");
      Rec.active ()) in
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "after") ~value:(fun () -> Some "d");
  close_proof ();
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "closed") ~value:(fun () -> Some "d");
  let p = List.hd (the_file ()).R.proofs in
  mk_bool_test "recorder-scope"
    "only reads between open and close are kept; without_recording drops its reads"
    (not during && List.map (fun r -> r.R.key) p.R.reads = [ "inside"; "after" ])

(* A read is recorded once per (row, channel, key); its key and value are not
   computed when the recorder is off or outside a proof. *)
let dedup =
  start ();
  let calls = ref 0 in
  let key () = incr calls; "Top.x" in
  open_proof ();
  Rec.read ~row:"1" ~channel:"constant" ~key ~value:(fun () -> Some "d1");
  Rec.read ~row:"1" ~channel:"constant" ~key ~value:(fun () -> Some "d1");
  Rec.read ~row:"1" ~channel:"inductive" ~key ~value:(fun () -> Some "d1");
  let in_proof = !calls in
  close_proof ();
  Rec.read ~row:"1" ~channel:"constant" ~key ~value:(fun () -> Some "d1");
  let p = List.hd (the_file ()).R.proofs in
  mk_bool_test "recorder-dedup"
    "a repeated read is stored once; no key is computed outside a proof"
    (List.length p.R.reads = 2 && in_proof = 3 && !calls = 3)

(* A changed value for one key makes the proof ineligible: replay cannot
   reproduce a read whose value moved while the proof ran. *)
let value_changed =
  start ();
  open_proof ();
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "Top.x") ~value:(fun () -> Some "d1");
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "Top.x") ~value:(fun () -> Some "d2");
  close_proof ();
  let p = List.hd (the_file ()).R.proofs in
  mk_bool_test "recorder-value-changed"
    "a key whose value changes inside the proof makes the proof ineligible"
    (List.exists (fun i -> i.R.reason = "read_changed") p.R.ineligible)

let ineligible_reasons =
  start ();
  open_proof ();
  Rec.ineligible ~reason:"catchall" ~detail:"pretyping/evarconv.ml:285";
  Rec.ineligible ~reason:"catchall" ~detail:"pretyping/evarconv.ml:285";
  Rec.ineligible ~reason:"abstract" ~detail:"abstract";
  close_proof ();
  let p = List.hd (the_file ()).R.proofs in
  mk_bool_test "recorder-ineligible"
    "ineligibility reasons are kept once each, in order"
    (List.map (fun i -> (i.R.reason, i.R.detail)) p.R.ineligible
     = [ ("catchall", "pretyping/evarconv.ml:285"); ("abstract", "abstract") ])

(* A proof closed with Admitted, or abandoned, still gets an entry. *)
let admitted =
  start ();
  open_proof ~name:"Top.File.adm" ();
  close_proof ~closer:"Admitted" ~kernel_check:false ();
  let p = List.hd (the_file ()).R.proofs in
  mk_bool_test "recorder-admitted"
    "an Admitted proof has an entry with its closer and no kernel check"
    (p.R.closer = "Admitted" && not p.R.kernel_check)

(* A nested proof (abstract, Program obligation) does not open a second entry;
   the outer proof is marked ineligible instead. *)
let nested =
  start ();
  open_proof ~name:"Top.File.outer" ();
  open_proof ~name:"Top.File.inner" ();
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "in_inner") ~value:(fun () -> Some "d");
  close_proof ();
  let name_after_inner = Rec.current_name () in
  close_proof ();
  let f = the_file () in
  let p = List.hd f.R.proofs in
  mk_bool_test "recorder-nested"
    "a nested proof writes no entry of its own and makes the outer one ineligible"
    (List.length f.R.proofs = 1 && p.R.name = "Top.File.outer"
     && name_after_inner = Some "Top.File.outer"
     && List.exists (fun i -> i.R.reason = "nested_proof") p.R.ineligible
     && List.exists (fun r -> r.R.key = "in_inner") p.R.reads)

let start_tables =
  start ~tables:true ();
  Rec.register_tables (fun () ->
      [ R.{ row = "7"; channel = "hint_db"; key = "core"; value = Some (String.make 32 'e') } ]);
  open_proof ();
  close_proof ();
  let p = List.hd (the_file ()).R.proofs in
  let () = start ~tables:false () in
  Rec.register_tables (fun () -> assert false);
  open_proof ();
  close_proof ();
  let q = List.hd (the_file ()).R.proofs in
  mk_bool_test "recorder-start-tables"
    "with tables_at_start, every table is listed at the proof's start; without it, none is read"
    (List.map (fun r -> r.R.key) p.R.start_tables = [ "core" ] && q.R.start_tables = [])

(* The sentence that opens a proof is the proof's first sentence, and the
   one that closes it is its last. A sentence outside a proof is dropped,
   and its digest is never computed. *)
let sentences =
  start ();
  let computed = ref [] in
  let run name f = Rec.sentence (fun () -> computed := name :: !computed; name) f in
  run "before" (fun () -> ());
  run "statement" (fun () -> open_proof ());
  run "tactic" (fun () -> ());
  let a = run "closer" (fun () -> close_proof (); 7) in
  run "after" (fun () -> ());
  let p = List.hd (the_file ()).R.proofs in
  let expected = R.digest_value [ "statement"; "tactic"; "closer" ] in
  mk_bool_test "recorder-sentences"
    "the statement's and the closer's sentences belong to the proof; others are dropped"
    (a = 7 && List.rev !computed = [ "statement"; "tactic"; "closer" ] && p.R.sentences = expected)

(* Writes are collected while a proof is open, inside without_recording too. *)
let writes =
  start ();
  Rec.write_scheme "dropped";
  open_proof ();
  Rec.write_universes ~levels:[ "Top.1" ] ~constraints:[ "Top.1 < Top.2" ];
  Rec.write_counters [ ("evar", 2); ("univ", 0) ];
  Rec.without_recording (fun () ->
      Rec.write_scheme "Top.t_rect";
      Rec.write_constraint_source "Top.lemma";
      Rec.write_warning ~name:"deprecated-reference" ~message:"gone";
      Rec.write_counters [ ("evar", 3) ]);
  close_proof ();
  let w = (List.hd (the_file ()).R.proofs).R.writes in
  mk_bool_test "recorder-writes"
    "writes are collected while a proof is open, counters are summed, and a zero advance is dropped"
    (w.R.universe_levels = [ "Top.1" ] && w.R.constraints = [ "Top.1 < Top.2" ]
     && w.R.schemes = [ "Top.t_rect" ] && w.R.constraint_sources = [ "Top.lemma" ]
     && w.R.warnings_raised = [ ("deprecated-reference", "gone") ]
     && w.R.counters = [ ("evar", 5) ])

let tests =
  [ inert; one_proof; outside; dedup; value_changed; ineligible_reasons; admitted; nested; start_tables;
    sentences; writes ]

let _ = run_tests __FILE__ log_out_ch tests
