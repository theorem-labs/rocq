open Utest

(* BET-84 P3. The defect these tests exist for: a replay that accepts a
   stored term after an input the proof read has changed. Replay is sound
   only because every recorded read is checked again, so each way of
   failing to check one is a case here:
     - the value a read gives now is a different one;
     - the channel has no evaluator in this Rocq, so nothing can check it;
     - an evaluator cannot answer;
     - a provider that answered at the registration answers no longer.
   Each must leave the proof to its tactics. Written in place of the
   cross-family review, which cannot run until 2026-10-30 17:45Z: reviewed
   same-family only, cross-family unavailable until 2026-10-30 17:45Z. *)

let log_out_ch = open_log_out_ch __FILE__

module R = Proof_record
module Replay = Proof_replay

let toolchain : R.toolchain = R.{
  binary = "0123456789abcdef0123456789abcdef";
  plugins = [];
  load_order = [];
  warnings = "";
  safe_deps = [];
  stack_limit = "unlimited";
}

let header : R.header = R.{
  version = R.format_version;
  library = "Top.File";
  source = "dir/File.v";
  source_digest = String.make 32 'a';
  toolchain;
  memory_cap = "max";
  rlimit_as = "unlimited";
  rlimit_data = "unlimited";
  overcommit_memory = "0";
  skip_qed_typecheck = false;
  tables_at_start = true;
}

let statement = String.make 32 'b'
let position : R.position = R.{ module_path = "Top.File"; section_path = "" }
let sentences = [ String.make 32 'c'; String.make 32 'd' ]

let no_writes : R.writes = R.{
  universe_levels = []; counters = []; constraints = []; schemes = [];
  constraint_sources = []; warnings_raised = [];
}

(* The one proof of the record: it read one constant, with the digest the
   evaluator below gives while [current] holds it. *)
let the_read : R.read =
  R.{ row = "1"; channel = "unit_test_channel"; key = "Top.File.k"; value = Some (String.make 32 'e') }

let proof : R.proof = R.{
  name = "Top.File.lemma";
  statement;
  sentences = R.digest_value sentences;
  closer = "Qed";
  toolchain_key = R.toolchain_key toolchain;
  position;
  ineligible = [];
  reads = [ the_read ];
  start_tables = [];
  writes = no_writes;
  kernel_check = true;
  wall_s = 2.0;
  cpu_s = 2.0;
  span = Some (0, 10);
  replay = Some "AQIDBA==";
}

let trailer : R.trailer =
  R.{ file_wall_s = 3.0; file_cpu_s = 3.0; peak_rss_kb = 1024; proof_count = 1 }

let write_record ?(proof = proof) () =
  let buf = Buffer.create 1024 in
  R.output_header buf header;
  R.output_proof buf proof;
  R.output_trailer buf { trailer with proof_count = 1 };
  let path = Filename.temp_file "proof-replay" ".jsonl" in
  let oc = open_out_bin path in
  output_string oc (Buffer.contents buf);
  close_out oc;
  path

(* What the one channel is worth now. The tests move it. *)
let current = ref (Replay.Value (Some (String.make 32 'e')))

let () = Replay.register_evaluator "unit_test_channel" (fun _ -> !current)

(* The layer that owns the stored term accepts it; [Declare] does this in
   the real compile. Without one, every proof misses, which is the
   fail-closed default. *)
let () = Replay.register_precheck (fun _ -> true)

let setup ?(budget = None) ?(proof = proof) ?(now = toolchain) () =
  let path = write_record ~proof () in
  Replay.configure ~source:(Replay.Record_file path) ~ratio:2.0 ~budget ~peak_limit_kb:None;
  Replay.start ~library:"Top.File" ~toolchain:(fun () -> now);
  Sys.remove path

let decide ?(name = "Top.File.lemma") ?(closer = "Qed") ?(sentences = sentences) () =
  Replay.open_proof ~name
    ~statement:(fun () -> statement)
    ~position:(fun () -> position)
    ~toolchain_key:(fun () -> R.toolchain_key toolchain);
  Replay.decide ~sentences ~closer

let hits () =
  setup ();
  decide () <> None

(* A read that gives the same value now is the only way to a hit. *)
let unchanged_read_hits =
  mk_bool_test "proof-replay-hit"
    "a proof whose every recorded read gives the same value replays its stored term"
    (current := Replay.Value (Some (String.make 32 'e'));
     hits ())

let changed_read_misses =
  mk_bool_test "proof-replay-changed-read"
    "a read that gives another value now, or absent, leaves the proof to its tactics"
    (current := Replay.Value (Some (String.make 32 'f'));
     let moved = hits () in
     current := Replay.Value None;
     let absent = hits () in
     current := Replay.Value (Some (String.make 32 'e'));
     (not moved) && not absent)

let unknown_read_misses =
  mk_bool_test "proof-replay-unknown-read"
    "an evaluator that cannot answer leaves the proof to its tactics"
    (current := Replay.Unknown;
     let unknown = hits () in
     current := Replay.Value (Some (String.make 32 'e'));
     not unknown)

let unevaluated_channel_misses =
  let other = R.{ the_read with channel = "unit_test_channel_with_no_evaluator" } in
  mk_bool_test "proof-replay-no-evaluator"
    "a channel no evaluator covers is a miss, never a match"
    (setup ~proof:R.{ proof with reads = [ other ] } ();
     decide () = None)

let key_items_miss =
  mk_bool_test "proof-replay-key"
    "another closer, another sentence, another name: each is a miss"
    (let bad_closer = (setup (); decide ~closer:"Admitted" ()) in
     let bad_sentences = (setup (); decide ~sentences:[ String.make 32 'z' ] ()) in
     let bad_name = (setup (); decide ~name:"Top.File.other" ()) in
     bad_closer = None && bad_sentences = None && bad_name = None)

let ineligible_misses =
  mk_bool_test "proof-replay-ineligible"
    "a proof the registration marked ineligible, or that stored no term, is never replayed"
    (setup ~proof:R.{ proof with ineligible = [ { reason = "timeout"; detail = "1." } ] } ();
     let marked = decide () in
     setup ~proof:R.{ proof with replay = None } ();
     let no_term = decide () in
     marked = None && no_term = None)

(* A term another Rocq stored is never replayed by this one. The binary is
   key item 2, so a record from another build misses on the key, and so
   does one from another plugin set, another [-w], another safe-dependency
   set or another stack limit. An object built before a kernel fix can
   fail coqchk after it, so this refusal is the one that keeps a replay
   from carrying a term across a Rocq that changed. *)
let other_toolchain_misses =
  let key = R.toolchain_key toolchain in
  let case k = (setup ~proof:R.{ proof with toolchain_key = k } (); decide ()) in
  mk_bool_test "proof-replay-other-toolchain"
    "a record another Rocq, plugin set, warning set, safe-dependency set or stack limit made is refused"
    (case R.{ key with binary = String.make 32 '0' } = None
     && case R.{ key with plugins = String.make 32 '1' } = None
     && case R.{ key with load_order = String.make 32 '2' } = None
     && case R.{ key with warnings = "+all" } = None
     && case R.{ key with safe_deps = String.make 32 '3' } = None
     && case R.{ key with stack_limit = "8388608" } = None
     && (setup (); decide () <> None))

(* The same refusal for the whole file, before any proof is declared: a
   record whose header names another binary, plugin set, library order,
   safe-dependency set or stack limit leaves every proof of the file to its
   tactics, and the summary says why. A required library whose CONTENTS
   changed is not a refusal: its digest moves, its name and order do not. *)
let other_toolchain_refuses_file =
  let case now = (setup ~now (); (Replay.refused (), decide ())) in
  let refused (r, d) = r = Some "toolchain" && d = None in
  mk_bool_test "proof-replay-other-toolchain-file"
    "a record another toolchain made is refused for the whole file, with the reason named"
    (refused (case R.{ toolchain with binary = String.make 32 '0' })
     && refused (case R.{ toolchain with plugins = [ ("rocq-runtime.plugins.ltac", String.make 32 '1') ] })
     && refused (case R.{ toolchain with load_order = [ ("Other.Lib", String.make 32 '2') ] })
     && refused (case R.{ toolchain with safe_deps = [ "Other.Lib" ] })
     && refused (case R.{ toolchain with stack_limit = "8388608" })
     && (let r, d = case toolchain in r = None && d <> None))

(* The charged clock. A replayed proof costs no time, so the compile
   charges r times the seconds the registration spent, and stops the file
   at the budget as stock's own timeout stops it. *)
let charged_clock =
  mk_bool_test "proof-replay-budget"
    "the charge is r times the registered seconds, and the budget ends the file"
    (current := Replay.Value (Some (String.make 32 'e'));
     setup ~budget:(Some 3.0) ();
     let before = match Replay.check_budget () with () -> true | exception Replay.Budget_exhausted -> false in
     let hit = decide () <> None in
     (* r = 2.0 and the proof's registered wall is 2.0 s, so the charge is
        4.0 s, past the 3 s budget. *)
     let after =
       match Replay.check_budget () with () -> false | exception Replay.Budget_exhausted -> true
     in
     before && hit && after)

let summary_counts =
  mk_bool_test "proof-replay-summary"
    "the summary names each proof's outcome, and the channel a read miss came from"
    (current := Replay.Value (Some (String.make 32 'f'));
     setup ();
     let _ = decide () in
     let path = Filename.temp_file "proof-replay" ".json" in
     Replay.write_summary path;
     let ic = open_in_bin path in
     let text = really_input_string ic (in_channel_length ic) in
     close_in ic;
     Sys.remove path;
     current := Replay.Value (Some (String.make 32 'e'));
     let has s = Option.has_some (String.index_opt text '{') && CString.string_contains ~where:text ~what:s in
     has "\"hits\":0" && has "\"outcome\":\"read\"" && has "unit_test_channel")

let tests =
  [ unchanged_read_hits; changed_read_misses; unknown_read_misses; unevaluated_channel_misses;
    key_items_miss; ineligible_misses; other_toolchain_misses; other_toolchain_refuses_file;
    charged_clock; summary_counts ]

let _ = run_tests __FILE__ log_out_ch tests
