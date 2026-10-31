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
  constraint_sources = [];
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

let record_bytes ?(header = header) ?(proof = proof) () =
  let buf = Buffer.create 1024 in
  R.output_header buf header;
  R.output_proof buf proof;
  R.output_trailer buf { trailer with proof_count = 1 };
  Buffer.contents buf

(* The record is written read-only, as a registration's is: a record the
   compiling user can write is refused (review P3Deep F1). *)
let write_record ?(header = header) ?(proof = proof) ?(perm = 0o444) () =
  let path = Filename.temp_file "proof-replay" ".jsonl" in
  let oc = open_out_bin path in
  output_string oc (record_bytes ~header ~proof ());
  close_out oc;
  Unix.chmod path perm;
  path

(* What the one channel is worth now. The tests move it. *)
let current = ref (Replay.Value (Some (String.make 32 'e')))

let () = Replay.register_evaluator "unit_test_channel" (fun _ -> !current)

(* The layer that owns the stored term accepts it; [Declare] does this in
   the real compile. Without one, every proof misses, which is the
   fail-closed default. *)
let () = Replay.register_precheck (fun _ -> true)

let setup ?(budget = None) ?(proof = proof) ?(now = toolchain) ?(header = header) ?(perm = 0o444)
    ?digest ?(library = "Top.File") ?(source = None) () =
  let path = write_record ~header ~proof ~perm () in
  (* The digest is mandatory; by default the test passes the right one. *)
  let digest = match digest with
    | Some d -> d
    | None -> Some (Proof_sha256.digest_hex (record_bytes ~header ~proof ()))
  in
  Replay.configure ~source:(Replay.Record_file path) ~ratio:2.0 ~budget ~peak_limit_kb:None ~digest;
  Replay.start ~library ~source ~toolchain:(fun () -> now);
  Unix.chmod path 0o644;
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

(* The record is trusted only when it is bound to this compile (review
   P3Deep F1): its SHA-256 equals the digest the engine passes, the
   compiling user cannot write it, and its header names this library. Each
   case must refuse the whole file and name the reason; the control with
   the right digest must hit. Without the binding checks, each case hits. *)
let binding_refusals =
  let case ?perm ?digest ?library ?header () =
    setup ?perm ?digest ?library ?header (); (Replay.refused (), decide ())
  in
  let refused reason (r, d) = r = Some reason && d = None in
  let right = Some (Proof_sha256.digest_hex (record_bytes ())) in
  mk_bool_test "proof-replay-binding"
    "a record whose digest differs, that the compiling user can write, or that names another library is refused"
    (refused "digest" (case ~digest:(Some (String.make 64 '0')) ())
     && refused "digest" (case ~digest:None ())
     && refused "writable" (case ~perm:0o644 ())
     && refused "library" (case ~library:"Top.Other" ())
     && refused "format" (case ~header:R.{ header with tables_at_start = false } ())
     && (let r, d = case ~digest:right () in r = None && d <> None))

(* The overcommit guard is fail-closed (review P3Deep F6): a value the
   registration could not read refuses, as "2" does. *)
let overcommit_unknown_refuses =
  mk_bool_test "proof-replay-overcommit-unknown"
    "a record made where vm.overcommit_memory could not be read is refused"
    (setup ~header:R.{ header with overcommit_memory = "unknown" } ();
     Replay.refused () = Some "overcommit" && decide () = None)

(* The SHA-256 the binding uses is the standard one: FIPS 180-4's own
   test vectors. *)
let sha256_vectors =
  mk_bool_test "proof-replay-sha256"
    "the record digest is SHA-256: the FIPS 180-4 test vectors"
    (Proof_sha256.digest_hex "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
     && Proof_sha256.digest_hex "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
     && Proof_sha256.digest_hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
        = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
     && Proof_sha256.digest_hex (String.make 1_000_000 'a')
        = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0")

(* The whole-file refusal (Claude review of c2190e74e0, P1): after the first
   closer, a command that can rebind a Rocqlib name or load code refuses the
   file. Before it, nothing has been replayed, so it is allowed; comments and
   strings are not commands. *)
let rebind_scan =
  let s = Replay.scan_late_rebind in
  let end_ = "End (of a module, or of a section that loads or imports)" in
  mk_bool_test "proof-replay-rebind-scan"
    "a Register, Require, Load, Declare, Import, Export, Include, Module, Reset, Back, BackTo, or an End that can rebind, after the first closer, is found with its line"
    (s "Lemma a : True.\nProof. exact I. Qed.\nRegister x as core.eq.type.\n" = Some ("Register", 3)
     && s "Register x as core.eq.type.\nLemma a : True.\nProof. exact I. Qed.\n" = None
     && s "Lemma a : True.\nProof. exact I. Save a.\nRequire Import Foo.\n" = Some ("Require", 3)
     && s "Lemma a : True. Proof. exact I. Qed. Declare ML Module \"p\"." = Some ("Declare", 1)
     && s "Lemma a : True. Proof. exact I. Qed. (* Register (* nested *) Require *) Lemma b : True. Qed." = None
     && s "Lemma a : True. Qed. Lemma b : True. Proof. idtac \"Require \"\"Load\"\"\". Qed." = None
     && s "Section S. Register x as core.eq.type. Lemma a : True. Qed.\nEnd S." = Some (end_, 2)
     && s "Section S. Lemma a : True. Qed. End S." = None
     && s "Lemma a : True. Qed. Module M. End M." = None
     && s "Lemma a : True. Qed. Module Import M. End M." = Some ("Import", 1)
     && s "Lemma a : True. Qed. Module M : T. End M." = Some ("Module", 1)
     && s "Lemma a : True. Qed. Module F (X : T). End F." = Some ("Module", 1)
     && s "Lemma a : True. Qed. Module Type T. End T." = Some ("Module", 1)
     && s "Module M. Include N. Lemma a : True. Qed. End M." = Some (end_, 1)
     && s "Module M. Lemma a : True. Qed. End M." = None
     && s "Lemma a : True. Qed. Module N := F X." = Some ("Module", 1)
     && s "Lemma a : True. Qed. Timeout 1Register x as core.eq.type." = Some ("Register", 1)
     && s "Module M : T. Lemma a : True. Qed. End M." = Some (end_, 1)
     && s "Section S. Import M. Lemma a : True. Qed. End S." = Some (end_, 1)
     && s "Section S. Section T. Import M. End T. Lemma a : True. Qed. End S." = Some (end_, 1)
     && s "Lemma a : True. Qed. Export M." = Some ("Export", 1)
     && s "Lemma a : True. Qed. Include M." = Some ("Include", 1)
     && s "Lemma a : True. Qed. Module M (* x. *) := F E." = Some ("Module", 1)
     && s "Declare Module M : T. Section S. Lemma a : True. Qed. End S." = None
     && s "Lemma a : True. Qed. Timeout 1_Register x as core.eq.type." = Some ("Register", 1)
     && s "Lemma a : True. Qed. Timeout 0x1Register x as core.eq.type." = Some ("Register", 1)
     && s "Section S. Import M. Print Section S. Lemma a : True. Qed. End S." = Some (end_, 1)
     && s "Section S. Lemma a : True. Qed. Fail End S. End S." = None
     && s "Module M := F X. Section S. Lemma a : True. Qed. End S." = None
     && s "Module M (* x. *) := F E. Section S. Lemma a : True. Qed. End S." = None
     && s "#[local] Section S. Import M. Lemma a : True. Qed. End S." = Some (end_, 1)
     && s "Lemma a : True. Qed. Timeout 0xaRegister x as core.eq.type." = Some ("Register", 1)
     && s "Section S. Import M. Section T. Timeout 1End T. Lemma a : True. Qed. End S." = Some (end_, 1)
     && s "Section S. Import M. Timeout 1Print Section S. Lemma a : True. Qed. End S." = Some (end_, 1)
     && s "Lemma a : True. Qed. Timeout 1e5 Register x as core.eq.type." = Some ("Register", 1)
     && s "Section S. Import M. Lemma a : True. Qed. Check (x .. Section y). End S." = Some (end_, 1)
     && s "Section S. Import M. #[program (* ] Section *)] Definition d := 0. Lemma a : True. Qed. End S." = Some (end_, 1)
     && s "Section S. Import M. #[warnings=\"]\"] Definition d := 0. Lemma a : True. Qed. End S." = Some (end_, 1)
     && s "Lemma a : True. Qed. Import M." = Some ("Import", 1)
     && s "Lemma a : True. Qed. Load \"f\"." = Some ("Load", 1)
     && s "Lemma Requires : True. Qed." = None
     && s "Lemma a : True. Qed. Reset a." = Some ("Reset", 1)
     && s "Lemma a : True. Qed. Reset Initial." = Some ("Reset", 1)
     && s "Lemma a : True. Qed. Back." = Some ("Back", 1)
     && s "Lemma a : True. Qed. Back 2." = Some ("Back", 1)
     && s "Lemma a : True. Qed. BackTo 3." = Some ("BackTo", 1)
     && s "Definition d := 0. Reset d. Lemma a : True. Qed." = None
     && s "Section S. Reset S. Section T. Lemma a : True. Qed. End T." = Some ("End (after a Reset or Back)", 1)
     && s "Lemma Resets : True. Qed." = None
     && s "" = None)

(* The scan also gives the offset of the LAST late command: every proof that
   opens before it runs, every proof after it may replay. *)
let late_events_scan =
  let s = Replay.scan_late_events in
  mk_bool_test "proof-replay-late-events-scan"
    "the first late command keeps its line, and the last one's offset is the start of its word"
    (s "Lemma a : True. Qed. Import M. Lemma b : True. Qed. Export N. Lemma c : True. Qed."
     = (Some ("Import", 1), Some 52)
     && s "Lemma a : True. Qed. Lemma b : True. Qed." = (None, None)
     && s "Require Import M. Lemma a : True. Qed." = (None, None)
     && s "Lemma a : True. Qed. Register x as core.eq.type." = (Some ("Register", 1), Some 21)
     && s "Lemma a : True. Qed. Module M. Import N. End M." = (Some ("Import", 1), Some 41)
     && Replay.scan_late_events ~imports_late:false "Lemma a : True. Qed. Module M. Import N. End M."
        = (None, None)
     && Replay.scan_late_events ~imports_late:false "Lemma a : True. Qed. Import N. Require M."
        = (Some ("Require", 1), Some 31)
     && s "Lemma a : True. Qed. Module M : T. End M." = (Some ("Module", 1), Some 35)
     (* After a Reset the frames are not followed: the plain module's End,
        whose frame the Reset popped, still counts. *)
     && s "Module M. Import N. Lemma a : True. Qed. Section S. Reset S. End M."
        = (Some ("Reset", 1), Some 61)
     && s "Lemma a : True. Qed. Reset a. Lemma b : True. Qed." = (Some ("Reset", 1), Some 21))

(* The hit hooks see the replayed proof's reads, and only on a hit (Rocqlib
   marks the lib_ref keys observed through one). *)
let hit_hook_seen : R.read list option ref = ref None

let () = Replay.register_hit_hook (fun reads -> hit_hook_seen := Some reads)

let hit_hook_runs =
  mk_bool_test "proof-replay-hit-hook"
    "a hit hands the replayed proof's reads to the hit hooks; a miss does not"
    (current := Replay.Value (Some (String.make 32 'f'));
     hit_hook_seen := None;
     let _ = hits () in
     let after_miss = !hit_hook_seen in
     current := Replay.Value (Some (String.make 32 'e'));
     let _ = hits () in
     after_miss = None && !hit_hook_seen = Some [ the_read ])

(* A read miss says why: the value changed, the evaluator could not answer,
   or the channel has no evaluator. *)
let miss_reason =
  let summary_text () =
    let path = Filename.temp_file "proof-replay" ".json" in
    Replay.write_summary path;
    let ic = open_in_bin path in
    let text = really_input_string ic (in_channel_length ic) in
    close_in ic; Sys.remove path; text
  in
  let why () = summary_text () in
  let has text s = CString.string_contains ~where:text ~what:s in
  mk_bool_test "proof-replay-miss-reason"
    "a read miss names changed, unknown or no_evaluator"
    (current := Replay.Value (Some (String.make 32 'f'));
     let _ = hits () in
     let changed = why () in
     current := Replay.Unknown;
     let _ = hits () in
     let unknown = why () in
     current := Replay.Value (Some (String.make 32 'e'));
     setup ~proof:R.{ proof with reads = [ { the_read with channel = "unit_test_channel_with_no_evaluator" } ] } ();
     let _ = decide () in
     let none = why () in
     has changed "\"why\":\"changed\"" && has unknown "\"why\":\"unknown\""
     && has none "\"why\":\"no_evaluator\"")

(* A plugin this tree does not build can add commands and closures no read
   sees: while one is loaded, no proof is replayed, and the summary names it. *)
let plugin_audit_refuses =
  let tc = R.{ toolchain with plugins = [ ("unit.test.unaudited", "d") ] } in
  let h = R.{ header with toolchain = tc } in
  let p = R.{ proof with toolchain_key = R.toolchain_key tc } in
  let attempt () =
    setup ~header:h ~proof:p ~now:tc ();
    Replay.open_proof ~name:"Top.File.lemma" ~statement:(fun () -> statement)
      ~position:(fun () -> position) ~toolchain_key:(fun () -> R.toolchain_key tc);
    Replay.decide ~sentences ~closer:"Qed"
  in
  mk_bool_test "proof-replay-plugin-audit"
    "while a plugin outside the audited set is loaded, no proof is replayed"
    (current := Replay.Value (Some (String.make 32 'e'));
     Replay.register_plugin_audit (fun name -> not (String.equal name "unit.test.unaudited"));
     let refused = attempt () in
     Replay.register_plugin_audit (fun _ -> true);
     let audited = attempt () in
     Replay.register_plugin_audit (fun _ -> false);
     refused = None && audited <> None)

(* rocq-read-file.plugin, which every BET memory image loads, is audited by
   name (Main's ruling): alone it leaves replay on; with any other plugin
   beside it, replay is off. *)
let plugin_allowlist =
  let with_plugins plugins =
    let tc = R.{ toolchain with plugins } in
    let h = R.{ header with toolchain = tc } in
    let p = R.{ proof with toolchain_key = R.toolchain_key tc } in
    setup ~header:h ~proof:p ~now:tc ();
    Replay.open_proof ~name:"Top.File.lemma" ~statement:(fun () -> statement)
      ~position:(fun () -> position) ~toolchain_key:(fun () -> R.toolchain_key tc);
    Replay.decide ~sentences ~closer:"Qed"
  in
  mk_bool_test "proof-replay-plugin-allowlist"
    "rocq-read-file.plugin alone leaves replay on; any other plugin beside it turns it off"
    (current := Replay.Value (Some (String.make 32 'e'));
     Replay.register_plugin_audit (fun _ -> false);
     let alone = with_plugins [ ("rocq-read-file.plugin", "d") ] in
     let other = with_plugins [ ("rocq-read-file.plugin", "d"); ("some.other.plugin", "d") ] in
     alone <> None && other = None)

(* A Require the text spells out in full carries its From prefix and its
   names; a late word the scan cannot read that way carries none, so it is
   late whatever is loaded. *)
let require_scan =
  let rq ?(imports_late = false) text =
    List.map (fun (c : Replay.late_command) -> c.lc_require)
      (snd (Replay.scan_late_commands ~imports_late text))
  in
  let r ?from names = Some Replay.{ rq_from = from; rq_names = names } in
  let after_qed s = "Lemma a : True. Qed. " ^ s in
  mk_bool_test "proof-replay-require-scan"
    "a Require spelled out in full carries its From prefix and names; other late words carry none"
    (rq (after_qed "Require A.") = [ r [ "A" ] ]
     && rq (after_qed "From X.Y Require Import (* c *) A.B C(f, g(..)).") = [ r ~from:"X.Y" [ "A.B"; "C" ] ]
     && rq (after_qed "Time Require Export -(notations) A.") = [ r [ "A" ] ]
     && rq (after_qed "Fail Require (safe) Import A B'.") = [ r [ "A"; "B'" ] ]
     && rq (after_qed "#[local] Time From X Require\nA(* c *).") = [ r ~from:"X" [ "A" ] ]
     && rq ~imports_late:true (after_qed "Require Import A.") = [ None; r [ "A" ] ]
     && rq (after_qed "Require A. Register x as y.") = [ None; r [ "A" ] ]
     && rq (after_qed "Require x_Require.") = [ None; r [ "x_Require" ] ]
     && rq "Require A. Lemma a : True. Qed." = []
     && rq (after_qed "Require \xc3\x84.") = [ None ]
     && rq (after_qed "Require A\xc3\x84.") = [ None ]
     && rq (after_qed "Require Import.") = [ None ]
     && rq (after_qed "Require A \"s\".") = [ None ]
     && rq (after_qed "Require A.(B).") = [ None ]
     && rq (after_qed "Require (unsafe) A.") = [ None ]
     && rq (after_qed "Print Require.") = [ None ]
     && rq (after_qed "From X Print Require A.") = [ None ])

(* A later Require is late for a proof only while a library it names is not
   loaded, and a Require whose names do not resolve stays late. A Require
   that loads a library after a replayed proof stops the compile. *)
let loaded_libraries = ref []

let () =
  Replay.register_require_resolver (fun _from names ->
      if List.mem "Unresolved" names then None
      else Some (fun () -> List.for_all (fun n -> List.mem n !loaded_libraries) names))

let with_source text f =
  let path = Filename.temp_file "proof-replay" ".v" in
  let oc = open_out_bin path in
  output_string oc text;
  close_out oc;
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () -> f path)

let at_byte b = Replay.at_sentence (Loc.make_loc (b, b + 1))

(* The record's one proof, opened at byte [b] of [text]: replayed or not. *)
let replays_at text b =
  with_source text (fun path ->
      setup ~source:(Some path) ();
      at_byte b;
      decide () <> None)

let require_rule =
  (* The proof at byte 21 opens before the Require at byte 46, the one at
     byte 59 after it. *)
  let prefix = "Lemma a : True. Qed.\nLemma lemma : True. Qed.\n" in
  let text = prefix ^ "Require A B.\nLemma c : True. Qed.\n" in
  let detail () =
    let path = Filename.temp_file "proof-replay" ".json" in
    Replay.write_summary path;
    let ic = open_in_bin path in
    let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    Sys.remove path;
    s
  in
  let has text s = CString.string_contains ~where:text ~what:s in
  mk_bool_test "proof-replay-require-rule"
    "a later Require is late only while a library it names is not loaded or does not resolve"
    (current := Replay.Value (Some (String.make 32 'e'));
     loaded_libraries := [];
     let none_loaded = replays_at text 21 in
     let summary = detail () in
     loaded_libraries := [ "A" ];
     let one_loaded = replays_at text 21 in
     loaded_libraries := [ "A"; "B" ];
     let both_loaded = replays_at text 21 in
     let unresolved = replays_at (prefix ^ "Require Unresolved.\n") 21 in
     let other_late = replays_at (prefix ^ "Require A B.\nRegister x as y.\n") 21 in
     loaded_libraries := [];
     let after = replays_at text 59 in
     (not none_loaded) && (not one_loaded) && both_loaded && (not unresolved) && (not other_late) && after
     && has summary "\"refused_detail\":\"Require at line 3; no proof run; then 1 Require, late if it loads a library\"")

let require_tripwire =
  let text = "Lemma a : True. Qed.\nLemma lemma : True. Qed.\nRequire A.\n" in
  let stops () =
    match Replay.note_require ~already_loaded:false with
    | () -> false
    | exception e when CErrors.is_sync_anomaly e -> true
  in
  mk_bool_test "proof-replay-require-tripwire"
    "a Require that loads a library after a replayed proof stops the compile; before any replay it does not"
    (current := Replay.Value (Some (String.make 32 'e'));
     loaded_libraries := [ "A" ];
     with_source text (fun path ->
         setup ~source:(Some path) ();
         at_byte 46;
         let before_any_hit = not (stops ()) in
         setup ~source:(Some path) ();
         at_byte 21;
         let hit = decide () <> None in
         at_byte 46;
         Replay.note_require ~already_loaded:true;
         let after_hit = stops () in
         loaded_libraries := [];
         before_any_hit && hit && after_hit))

(* A process-wide fence (Proof_recorder.fence_tripped): a closure a plugin
   installs over Rocq's own, or a cache that no longer matches its table, is
   state no recorded read sees. Once one trips, no proof of the process is
   replayed, whatever its record holds, and the summary names the fence. The
   setter here stands for Evarconv.set_evar_conv: Rocq's own count is 0, so
   one call trips it. The fence is never cleared, so this test must run after
   every other one. It does because mk_bool_test evaluates its check when the
   test is DEFINED, and this is the last definition in the file; its place in
   [tests] below does not order anything. *)
let fence_refuses =
  let set = Proof_recorder.closure_setter ~what:"unit-test setter" ~stock:0 in
  mk_bool_test "proof-replay-fence"
    "after a process-wide fence trips, no proof of the process is replayed, and the summary says why"
    (current := Replay.Value (Some (String.make 32 'e'));
     let before = hits () in
     set ();
     setup ();
     let tripped = decide () in
     let path = Filename.temp_file "proof-replay" ".json" in
     Replay.write_summary path;
     let ic = open_in_bin path in
     let text = really_input_string ic (in_channel_length ic) in
     close_in ic;
     Sys.remove path;
     let later = hits () in
     let has s = CString.string_contains ~where:text ~what:s in
     before && tripped = None && (not later)
     && has "\"fence\":\"plugin_hook: unit-test setter\""
     && has "\"outcome\":\"ineligible\"" && has "\"hits\":0")

let tests =
  [ unchanged_read_hits; changed_read_misses; unknown_read_misses; unevaluated_channel_misses;
    key_items_miss; ineligible_misses; other_toolchain_misses; other_toolchain_refuses_file;
    binding_refusals; overcommit_unknown_refuses; sha256_vectors; charged_clock; summary_counts;
    rebind_scan; late_events_scan; hit_hook_runs; miss_reason; plugin_audit_refuses; plugin_allowlist;
    require_scan; require_rule; require_tripwire;
    (* Defined last in the file, which is what makes it run last. *)
    fence_refuses ]

let _ = run_tests __FILE__ log_out_ch tests
