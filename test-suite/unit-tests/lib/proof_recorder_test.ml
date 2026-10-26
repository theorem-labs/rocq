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
  Rec.close_proof ~closer ~kernel_check ~replay:None

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

(* Only the first value of a key is kept, and a repeated read does not
   compute its value again: that is what keeps a hot choke point cheap. *)
let first_value =
  start ();
  open_proof ();
  let values = ref 0 in
  let value d () = incr values; Some d in
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "Top.x") ~value:(value "d1");
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "Top.x") ~value:(value "d2");
  close_proof ();
  let p = List.hd (the_file ()).R.proofs in
  mk_bool_test "recorder-first-value"
    "a repeated key keeps its first value, and its value is computed once"
    (!values = 1 && p.R.ineligible = []
     && List.map (fun r -> r.R.value) p.R.reads = [ Some "d1" ])

(* read_by finds a repeat by its raw id, so neither the key nor the value is
   computed for it; a new proof starts with no id seen. *)
let read_by =
  start ();
  let keys = ref 0 and values = ref 0 in
  let read id =
    Rec.read_by ~row:"6" ~channel:"xref" ~id
      ~key:(fun () -> incr keys; String.concat "." id)
      ~value:(fun () -> incr values; Some "d") in
  open_proof ();
  read [ "Top"; "x" ];
  read [ "Top"; "x" ];
  read [ "Top"; "y" ];
  close_proof ();
  let first = (!keys, !values) in
  open_proof ~name:"Top.File.second" ();
  read [ "Top"; "x" ];
  close_proof ();
  let f = the_file () in
  mk_bool_test "recorder-read-by"
    "read_by computes key and value once per id per proof"
    (first = (2, 2) && (!keys, !values) = (3, 3)
     && List.map (fun p -> List.map (fun r -> r.R.key) p.R.reads) f.R.proofs
        = [ [ "Top.x"; "Top.y" ]; [ "Top.x" ] ])

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

(* The registry is global: the hint and typeclass modules linked into this
   test register their own tables when they load, so the test looks for its
   own entry among them, and counts the calls of its own source. *)
(* The registered tables are read at every proof's start, with or without the
   header's [tables_at_start]: a matcher compares [start_tables] like [reads],
   so a proof that misses them is not safe to replay. *)
let start_tables =
  let calls = ref 0 in
  Rec.register_tables (fun () ->
      incr calls;
      [ R.{ row = "7"; channel = "hint_db"; key = "test-db"; value = Some (String.make 32 'e') } ]);
  start ~tables:true ();
  open_proof ();
  close_proof ();
  let p = List.hd (the_file ()).R.proofs in
  let after_one = !calls in
  start ~tables:false ();
  open_proof ();
  close_proof ();
  let q = List.hd (the_file ()).R.proofs in
  let key r = r.R.key in
  mk_bool_test "recorder-start-tables"
    "every registered table is listed at each proof's start"
    (List.mem "test-db" (List.map key p.R.start_tables)
     && List.mem "test-db" (List.map key q.R.start_tables)
     && after_one = 1 && !calls = 2)

(* An Abort writes no entry and leaves the recorder free for the next proof.
   Without that, the aborted proof stays open and every proof after it in the
   file is taken for a nested one and loses its entry. *)
let dropped =
  start ();
  open_proof ~name:"Top.File.aborted" ();
  Rec.read ~row:"1" ~channel:"constant" ~key:(fun () -> "x") ~value:(fun () -> Some "d");
  Rec.drop_proof ();
  let free = Rec.current_name () in
  open_proof ~name:"Top.File.later" ();
  close_proof ();
  open_proof ~name:"Top.File.nested_outer" ();
  open_proof ~name:"Top.File.inner" ();
  Rec.drop_proof ();
  let still_open = Rec.current_name () in
  close_proof ();
  open_proof ~name:"Top.File.all" ();
  Rec.drop_all_proofs ();
  let f = the_file () in
  mk_bool_test "recorder-dropped"
    "a dropped proof writes no entry, and the proofs after it keep theirs"
    (free = None && still_open = Some "Top.File.nested_outer"
     && List.map (fun p -> p.R.name) f.R.proofs = [ "Top.File.later"; "Top.File.nested_outer" ]
     && f.R.trailer.R.proof_count = 2)

(* [Save id] declares [id], not the name the proof was opened with, and the
   record's name is what a matcher joins to the opaque term. *)
let renamed =
  start ();
  open_proof ~name:"Top.File.opening" ();
  open_proof ~name:"Top.File.inner" ();
  Rec.set_name "Top.File.not_this_one";
  close_proof ();
  Rec.set_name "Top.File.saved";
  close_proof ~closer:"Save" ();
  let p = List.hd (the_file ()).R.proofs in
  mk_bool_test "recorder-renamed"
    "the closer's name replaces the opening name, and a nested close does not"
    (p.R.name = "Top.File.saved" && p.R.closer = "Save")

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

(* A slot digests a value once and gives the same digest back while the
   value is the same one (by address); a different value is digested again.
   The test changes [a] in place between the two reads, which no global value
   a slot holds ever does: a slot that digested again would return the digest
   of the changed contents, so the reuse is seen. *)
let slot_reuse =
  start ();
  let s = Rec.slot () in
  let a = Sys.opaque_identity [| 1; 2; 3 |] and b = Sys.opaque_identity [| 4 |] in
  open_proof ();
  let d1 = Rec.digest_slot s ~what:"probe" a in
  a.(0) <- 9;
  let d2 = Rec.digest_slot s ~what:"probe" a in
  let d3 = Rec.digest_slot s ~what:"probe" b in
  close_proof ();
  let p = List.hd (the_file ()).R.proofs in
  mk_bool_test "recorder-slot-reuse"
    "a slot returns the kept digest for the same value and digests a new one"
    (d2 = d1 && d2 <> R.digest_value a && d3 = R.digest_value b && p.R.ineligible = [])

(* "unhashable" is one stand-in for every value that cannot be digested, so
   every proof that reuses a kept "unhashable" must be marked, not only the
   first: the second proof's read would otherwise match a replay where the
   value changed (Claude gate at 0f8d815732, finding 6). *)
let slot_unhashable =
  start ();
  let s = Rec.slot () in
  let v = Sys.opaque_identity (fun x -> x + 1) in
  open_proof ~name:"Top.File.first" ();
  let d1 = Rec.digest_slot s ~what:"probe" v in
  close_proof ();
  open_proof ~name:"Top.File.second" ();
  let d2 = Rec.digest_slot s ~what:"probe" v in
  close_proof ();
  let reasons p = List.map (fun i -> i.R.reason) p.R.ineligible in
  let f = the_file () in
  mk_bool_test "recorder-slot-unhashable"
    "a kept \"unhashable\" marks every proof that reuses it"
    (d1 = "unhashable" && d2 = "unhashable"
     && List.map reasons f.R.proofs = [ [ "unhashable" ]; [ "unhashable" ] ])

let tests =
  [ inert; one_proof; outside; dedup; first_value; read_by; ineligible_reasons; admitted; nested;
    start_tables; dropped; renamed; sentences; writes; slot_reuse; slot_unhashable ]

let _ = run_tests __FILE__ log_out_ch tests
