(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module R = Proof_record
module Scan = Proof_replay_scan

exception Budget_exhausted

(* The charged clock runs from this process's start, not from the moment
   the record was loaded: the engine's per-file timeout counts from the
   exec, and a later origin would let the charged kill fire after the
   engine's own (R1P4's cross-family review, 2026-10-25). This is
   evaluated when the unit is initialised, before any work of the
   compile. *)
let process_start = Unix.gettimeofday ()

type evaluation =
  | Unknown
  | Value of string option

(* The evaluators register when their module loads, before any compile, so
   the table is global and not part of a compile's state. *)
let evaluators : (string, string -> evaluation) Hashtbl.t = Hashtbl.create 64

let register_evaluator channel f = Hashtbl.replace evaluators channel f

(* A provider answers a whole set of reads at once: the channels that have
   no single read point, which the recorder also takes as one list. *)
let providers : (unit -> R.read list) Queue.t = Queue.create ()

let register_provider f = Queue.add f providers

(* Values known only to the code that opens the proof, such as the open
   proof's own [Proof using] set: given at its start, for its reads only. *)
let proof_provided : (string * string, string option) Hashtbl.t = Hashtbl.create 8

let provide ~channel ~key ~value = Hashtbl.replace proof_provided (channel, key) value

(* A counter kept in the Summary ([Summary.ref]): the evar and meta
   counters, the two hint counters, the SSR abstract counter. The STM
   rolls such a counter back with the rest of the Summary when the proof
   closes, so stock keeps only what the closing itself made. Measured on
   speed-r1, 2026-10-25: a proof whose record shows the evar counter
   advanced by 4 (meta by 2) left the next proof starting 2 above its own
   start in stock, the statement's and the closing's share. Moving such a
   counter after a replay put it at 5 where stock has 2, and every proof
   after a replayed one missed on its [counter_start] read. So replay
   leaves these counters alone: the declaration of the stored term makes
   the closing's share itself. If a case rolls back differently, the next
   proof's [counter_start] read differs and that proof runs its tactics. *)
let summary_counters : (string, unit) Hashtbl.t = Hashtbl.create 8

let register_summary_counter name = Hashtbl.replace summary_counters name ()

let can_advance name = Hashtbl.mem summary_counters name

(* The layer that made a stored term says, at the closer, whether this
   compile can use it. It is never a reason to use one. *)
let precheck : (string -> bool) ref = ref (fun _ -> false)

let register_precheck f = precheck := f

(* The last check, once every recorded read gave its value again: the layer
   that made the blob puts together what the declaration takes (the proof
   term the blob refers to, the universe state it rebuilds) and says whether
   it is the same as what the registration declared. A difference is a
   read miss, on the channel and for the reason it names. *)
let install_check : (string -> (string * string) option) ref = ref (fun _ -> Some ("stored_term", "unknown"))

let register_install_check f = install_check := f

let provided () =
  let tbl = Hashtbl.create 32 in
  Queue.iter
    (fun f ->
       List.iter
         (fun (r : R.read) -> Hashtbl.replace tbl (r.R.channel, r.R.key) r.R.value)
         (f ()))
    providers;
  tbl

type candidate = {
  c_proof : R.proof;
  c_offset : int;  (** where the proof's opening sentence starts *)
  c_provided : (string * string, string option) Hashtbl.t;
      (** the provided channels, read where the record read them: at the
          proof's start, not at its closer *)
}

type counts = {
  mutable n_proofs : int;
  mutable n_hits : int;
  mutable m_key : int;
  mutable m_read : int;
  mutable m_ineligible : int;
  mutable m_missing : int;
  mutable charged : float;  (** r times [registered] *)
  mutable registered : float;  (** the replayed proofs' registered wall seconds *)
  mutable outcomes : (string * string * (string * string) option) list;
      (** newest first; a read miss carries its channel and why it missed *)
  mutable fence : string option;
      (** the process-wide fence that refused a proof of this file, as
          ["reason: detail"] *)
}

type file_state = {
  f_index : (string, R.proof) Hashtbl.t;
  f_wall0 : float;
  f_refused : string option;
  f_refused_detail : string option;
      (** for ["rebind"], and for a file with a late command: the command and its line *)
  f_late : Scan.late_bound;
      (** the late commands, [Import] and [Export] counted: the bound once
          an export-locality registration is loaded *)
  f_late_no_imports : Scan.late_bound;
      (** the same, [Import] and [Export] not counted: the bound while no
          export-locality registration is loaded *)
  f_object : (string * string option) option;
      (** the registered [.vo] beside the record, and the SHA-256 of its
          opaque proofs the record's trailer holds *)
  mutable f_candidate : candidate option;
}

(* The charged clock's ratio and the per-file budget, from the command
   line; [None] when no replay is configured. *)
let clock : (float * float option) option ref = ref None

let configure_clock ~ratio ~budget = clock := Some (ratio, budget)

let state : file_state option ref = ref None

let counts = {
  n_proofs = 0; n_hits = 0; m_key = 0; m_read = 0; m_ineligible = 0; m_missing = 0;
  charged = 0.; registered = 0.; outcomes = []; fence = None;
}

let channel_miss : (string, int) Hashtbl.t = Hashtbl.create 16

(* For each proof that missed on a read: the read's key, its recorded value
   and its value now (absent when nothing answered), for the summary. *)
let miss_detail : (string, string * string option * string option) Hashtbl.t = Hashtbl.create 64

let enabled () = match !state with Some { f_refused = None; _ } -> true | _ -> false

let refused () = match !state with Some st -> st.f_refused | None -> None

(* A plugin outside the audited set (the plugins this tree builds) can add
   commands the source scan cannot read (one could rebind a Rocqlib name after
   a replayed proof), and closures no read sees. Loading one after the first
   closer is a [Require] or [Declare] the scan refuses; loading one before is
   caught here: while such a plugin is loaded, no proof is replayed (Claude
   delta review of 2daae0ed39, P2-1). The audit is the ltac plugin's list of
   audited packages (Tacinterp.audited_ml_tactic_plugins); until it registers,
   no plugin counts as audited. *)
let plugin_audit : (string -> bool) ref = ref (fun _ -> false)

(* Plugins from outside this tree that the replay audit has read, by exact
   findlib package name (Main's ruling, 2026-10-26).
   - [rocq-read-file.plugin]: theorem-labs/rocq-read-file at 68887ad, the
     commit the grading harness's Dockerfile pins. Every BET memory
     image loads it ([Declare ML Module "rocq-read-file.plugin"] in
     ReadFile.v). Audited 2026-10-26 (Claude delta review of a158379eb4,
     P2-1): it adds side-effect vernacular commands only (g_read_file.mlg),
     and no tactic, hook, closure setter, [register_ref], module import or
     cached [lib_ref].
   If BET's Dockerfile moves that pin, this audit must be redone before the
   entry is kept. *)
let audited_outside_tree = [ "rocq-read-file.plugin" ]

let register_plugin_audit f = plugin_audit := f

let toolchain_now : (unit -> R.toolchain) option ref = ref None

(* The toolchain's own fences, checked at each decision: a loaded plugin
   outside the audited set, or a digest of the binary or of a plugin's files
   that could not be read. The start refuses a record whose toolchain has
   such a digest ({!Proof_replay_record.load}); a plugin that loads after the start
   is caught here (reviewer round 2 of e560ab16e4, X5). *)
let toolchain_fence () =
  match !toolchain_now with
  | None -> None
  | Some tc ->
    let tc = tc () in
    match
      List.find_opt
        (fun (name, _) -> not (!plugin_audit name || List.mem name audited_outside_tree))
        tc.R.plugins
    with
    | Some (name, _) -> Some ("unaudited_plugin", name)
    | None -> Option.map (fun what -> ("toolchain_unknown", what)) (R.toolchain_unknown tc)

(* The layer that runs [Require] resolves one for a proof's decision: given
   the [From] prefix and the names as the text spells them, [None] when a
   name does not resolve, else a test of whether every library they name is
   loaded. Until one registers, no [Require] resolves, so each one is late. *)
let require_resolver : (string option -> string list -> (unit -> bool) option) ref =
  ref (fun _ _ -> None)

let register_require_resolver f = require_resolver := f

(* This file's late [Require]s, resolved, by offset. A name resolves the same
   at every decision: the load path does not change after startup, and coqc
   keeps the directory listings it read ([System.trust_file_cache]). *)
let require_resolutions : (int, (unit -> bool) option) Hashtbl.t = Hashtbl.create 16

let loads_nothing (offset, r) =
  let resolved =
    match Hashtbl.find_opt require_resolutions offset with
    | Some t -> t
    | None ->
      let t = !require_resolver r.Scan.rq_from r.Scan.rq_names in
      Hashtbl.add require_resolutions offset t;
      t
  in
  match resolved with None -> false | Some loaded -> loaded ()

(* An export-locality [Register] acts when its module is opened, so once one
   is loaded or declared in this process, [Import] and [Export] are late
   commands again ([Rocqlib] calls this). It is never reset: one process
   compiles one file. *)
let export_register_seen = ref false

let note_export_register () = export_register_seen := true

(* The location, in the file being compiled, of the sentence being run.
   The toplevel sets it before each sentence; a driver that does not leaves
   it before every late command, so a proof of such a file replays only when
   every late command is a [Require] that loads nothing. *)
let sentence_loc : Loc.t option ref = ref None

let sentence_offset () = match !sentence_loc with Some l -> l.Loc.bp | None -> -1

let at_sentence loc = sentence_loc := Some loc

let requires_seen : (int * bool) list ref = ref []

(* Where the first proof this file replayed opens. A replay relies on no
   later [Require] loading a library ({!opens_before_late_command}). *)
let first_hit : int option ref = ref None

(* A [Require] after a replayed proof that loads a library all the same
   means the decision read the text or the load path otherwise than the
   [Require] does. The proofs already replayed cannot run their tactics
   now, so the compile stops. *)
let note_require ~already_loaded =
  match !clock with
  | Some _ ->
    let here = sentence_offset () in
    requires_seen := (here, already_loaded) :: !requires_seen;
    (match !first_hit with
     | Some hit when hit <= here && not already_loaded ->
       CErrors.anomaly
         Pp.(str "Proof replay: the Require at byte " ++ int here ++ str " loads a library, after a proof"
             ++ str " replayed at byte " ++ int hit ++ str " on the condition that no later Require loads one.")
     | _ -> ())
  | None -> ()

(* How many proofs are open: a proof opened inside another one is part of
   it (the recorder keeps no entry of its own for it), so it is neither
   counted nor looked up. *)
let open_depth = ref 0

let close_proof () = if !open_depth > 0 then decr open_depth

let proof_open () = !open_depth > 0

let start ~record ~source_late ~toolchain =
  (* The counts, the charge and the outcomes belong to ONE file: a
     process that compiles a second file must not carry the first
     file's charge into its budget, nor its hits into its summary. *)
  counts.n_proofs <- 0;
  counts.n_hits <- 0;
  counts.m_key <- 0;
  counts.m_read <- 0;
  counts.m_ineligible <- 0;
  counts.m_missing <- 0;
  counts.charged <- 0.;
  counts.registered <- 0.;
  counts.outcomes <- [];
  counts.fence <- None;
  Hashtbl.reset channel_miss;
  Hashtbl.reset miss_detail;
  requires_seen := [];
  first_hit := None;
  Hashtbl.reset require_resolutions;
  Hashtbl.reset proof_provided;
  let index, registered_object, refusal =
    match record with
    | Ok r -> r.Proof_replay_record.index, Some r.Proof_replay_record.registered_object, None
    | Error reason -> Hashtbl.create 1, None, Some reason
  in
  (* The registration ran its process-wide cache fences from its start
     ([Proof_recorder.start]); a replay that does not run them would let
     a dirty history here match the clean one recorded there. From here
     on they run at each decision ({!decide}). *)
  let refusal, refused_detail, late, late_no_imports =
    match refusal with
    | Some _ -> refusal, None, Scan.no_late, Scan.no_late
    | None ->
      match source_late () with
      | Error () -> Some "rebind", Some "an unreadable source", Scan.no_late, Scan.no_late
      | Ok (Some { Scan.first = (cmd, line); late; late_no_imports }) ->
        let bound = function None -> "no proof" | Some b -> Printf.sprintf "proofs before byte %d" b in
        let requires =
          match List.length late_no_imports.Scan.lb_requires with
          | 0 -> ""
          | 1 -> "; then 1 Require, late if it loads a library"
          | k -> Printf.sprintf "; then %d Requires, each late if it loads a library" k
        in
        let detail =
          match late.Scan.lb_last with
          | Some last when late_no_imports.Scan.lb_last <> Some last ->
            Printf.sprintf "%s at line %d; %s run%s (byte %d after an export Register)"
              cmd line (bound late_no_imports.Scan.lb_last) requires last
          | _ -> Printf.sprintf "%s at line %d; %s run%s" cmd line (bound late_no_imports.Scan.lb_last) requires
        in
        None, Some detail, late, late_no_imports
      | Ok None -> None, None, Scan.no_late, Scan.no_late
  in
  if refusal = None then Proof_recorder.start_tracking ();
  toolchain_now := Some toolchain;
  sentence_loc := None;
  open_depth := 0;
  state := Some { f_index = index; f_wall0 = process_start; f_refused = refusal;
                  f_refused_detail = refused_detail; f_late = late;
                  f_late_no_imports = late_no_imports;
                  f_object = registered_object;
                  f_candidate = None }

let registered_object () = match !state with Some st -> st.f_object | None -> None

let check_budget () =
  match !clock, !state with
  | Some (_, Some budget), Some st ->
    if Unix.gettimeofday () -. st.f_wall0 +. counts.charged >= budget then raise Budget_exhausted
  | _ -> ()

(* What is left of the budget once the charge for the replayed proofs is
   taken off. A sentence runs under this as a timeout, so a proof that runs
   long is stopped inside it, where stock's own timeout stops it, and not
   only at the next sentence boundary. *)
let remaining_budget () =
  match !clock, !state with
  | Some (_, Some budget), Some st ->
    let left = budget -. (Unix.gettimeofday () -. st.f_wall0) -. counts.charged in
    Some (if left > 0.001 then left else 0.001)
  | _ -> None

(* {6 One proof} *)

let outcome name kind channel = counts.outcomes <- (name, kind, channel) :: counts.outcomes

let miss_key name = counts.m_key <- counts.m_key + 1; outcome name "key" None

let miss_read name channel why =
  counts.m_read <- counts.m_read + 1;
  outcome name "read" (Some (channel, why));
  Hashtbl.replace channel_miss channel (1 + Option.default 0 (Hashtbl.find_opt channel_miss channel))

(* Run on each hit with the replayed proof's reads, before the closer runs:
   the owner of a process-wide cache can treat what the proof read as
   looked up (Rocqlib marks its [lib_ref] keys observed, so a later
   rebinding of one trips its fence and no later proof is replayed). That
   stops later replays only; the late-command rule above (no proof replays
   before the file's last late command) is what keeps later tactics seeing
   what stock sees. The owner can also make the write to the cache that the
   skipped tactics made, when later tactics read it (zify copies its tables
   in [init_cache]; breadth audit gap BA4). *)
let hit_hooks : (R.read list -> unit) Queue.t = Queue.create ()

let register_hit_hook f = Queue.add f hit_hooks


let candidate_open () = match !state with Some { f_candidate = Some _; _ } -> true | _ -> false

(* The proof ran its tactics without a decision: its sentences were not the
   ones the record holds (a command inside the proof, a parse that stopped
   the buffering). That is key item 1. *)
let abandon () =
  match !state with
  | Some ({ f_candidate = Some c; _ } as st) -> st.f_candidate <- None; miss_key c.c_proof.R.name
  | Some _ | None -> ()

(* The proof stack is not part of this state. A sentence that drops proofs
   ([Abort All], [Reset], a [Succeed] or [Fail Fail] around a statement)
   closes none of them here, so without this every later proof of the file
   would be taken for a nested one and never replay (gate review R5). *)
let drop_all_proofs () =
  open_depth := 0;
  abandon ()

(* A write the declaration of the stored term does not make by itself: a
   counter that is not a Summary counter ([register_summary_counter]). The
   declaration makes the rest — the levels and constraints, the constraint
   sources, and the schemes, which travel with the term's side effects. A
   proof that raises a warning is ineligible ([CWarnings.warn]), so no
   warning is to be raised again.

   The universe and sort counters are not here: the stored term carries
   them, and the precheck compares them. *)
let unreplayable_writes (p : R.proof) =
  List.exists
    (fun (name, n) ->
       n > 0 && name <> "univ_level" && name <> "sort_quality" && not (can_advance name))
    p.R.writes.R.counters

(* A late command comes after the proof that opens here: one that is late
   whatever is loaded, or a [Require] that names a library not loaded now,
   or one that does not resolve. *)
let opens_before_late_command st =
  let bound = if !export_register_seen then st.f_late else st.f_late_no_imports in
  let here = sentence_offset () in
  (match bound.Scan.lb_last with Some last -> here <= last | None -> false)
  || List.exists (fun ((offset, _) as rq) -> here <= offset && not (loads_nothing rq)) bound.Scan.lb_requires

let open_proof ~name ~statement ~position ~toolchain_key =
  let nested = !open_depth > 0 in
  incr open_depth;
  match !state with
  | None | Some { f_refused = Some _; _ } -> ()
  | Some _ when nested -> ()
  | Some st ->
    st.f_candidate <- None;
    Hashtbl.reset proof_provided;
    counts.n_proofs <- counts.n_proofs + 1;
    (match Hashtbl.find_opt st.f_index name with
     | None -> counts.m_missing <- counts.m_missing + 1; outcome name "missing_record" None
     | Some _ when Proof_recorder.in_load () ->
       (* A [Load]ed file's proof runs inside the [Load] sentence, where the
          toplevel never decides it. A candidate set here would stay open
          after the [Load], and the toplevel would then keep the next
          sentences as this proof's (INFRA-361 gap 2). *)
       counts.m_ineligible <- counts.m_ineligible + 1;
       outcome name "ineligible" (Some ("load", "inside_load"))
     | Some _ when opens_before_late_command st ->
       counts.m_ineligible <- counts.m_ineligible + 1;
       outcome name "ineligible" (Some ("rebind", "before_late_command"))
     | Some p ->
       if p.R.ineligible <> [] || p.R.replay = None || unreplayable_writes p then begin
         counts.m_ineligible <- counts.m_ineligible + 1;
         outcome name "ineligible" None
       end
       else if p.R.statement <> statement () || p.R.position <> position ()
               || p.R.toolchain_key <> toolchain_key ()
       then miss_key name
       else
         (* The provided channels are the proof's START state, as the
            record takes them: the proof state the closer sees has moved
            past it (opening the proof makes evars and levels of its own).
            So they are read here, where the record read them. *)
         st.f_candidate <-
           Some { c_proof = p; c_offset = sentence_offset (); c_provided = provided () })

(* A counter's start (row 18) matters to a proof only through the fresh
   names it makes from it: a proof whose record shows no advance of a
   counter made none, so where that counter stood is not an input of the
   proof (fixture hint_added: a hint declared earlier moves the hint
   counter, and a later proof that declares no hint must still replay).
   The next proof that does advance the counter still reads its start, so a
   counter left elsewhere than stock leaves it is still caught there. The
   start keys are the counters' Summary names; the advances, the names the
   recorder writes. *)
let write_name_of_counter_start = function
  | "HINT-COUNTER" -> Some "hint_counter"
  | "REWHINT-COUNTER" -> Some "rewrite_hint_counter"
  | "evar counter" -> Some "evar"
  | "meta counter" -> Some "meta"
  | "univ_level" | "sort_quality" | "ssr_abstract_id" as k -> Some k
  | _ -> None

let counter_unmoved (p : R.proof) (r : R.read) =
  String.equal r.R.channel "counter_start"
  && (match write_name_of_counter_start r.R.key with
      | None -> false
      | Some name ->
        match List.assoc_opt name p.R.writes.R.counters with
        | None -> true
        | Some n -> n = 0)

(* Every read the registration made must give the same value now.

   A read is answered by the provider rows taken at the proof's start when
   one has its exact channel and key (the channels with no single read
   point, from the same function the recorder takes them from); otherwise
   by its channel's evaluator. A provider does not own its channel: a
   provider row keyed "" (a whole table) and an evaluator keyed by name can
   share a channel, and each answers its own keys. Before, a provider
   shadowed every key of its channel, so the per-constant
   [reduction_behaviour] reads always missed (review P3Deep F4). A read
   neither answers is a miss, and so is an evaluator that cannot answer.
   The one-value-per-channel check (dev/tools/census/replay_channels.py)
   makes sure a provider row and an evaluator of one channel are not two
   implementations of one value. *)
let first_read_mismatch (p : R.proof) ~at_start =
  let now (r : R.read) =
    match Hashtbl.find_opt proof_provided (r.R.channel, r.R.key) with
    | Some v -> Some (Value v)
    | None ->
      match Hashtbl.find_opt at_start (r.R.channel, r.R.key) with
      | Some v -> Some (Value v)
      | None ->
        match Hashtbl.find_opt evaluators r.R.channel with
        | None -> None
        | Some f -> Some (match f r.R.key with v -> v | exception _ -> Unknown)
  in
  let rec loop = function
    | [] -> None
    | (r : R.read) :: rest when counter_unmoved p r -> loop rest
    | (r : R.read) :: rest ->
      (match now r with
       | None -> Some (r.R.channel, "no_evaluator", (r.R.key, r.R.value, None))
       | Some Unknown -> Some (r.R.channel, "unknown", (r.R.key, r.R.value, None))
       | Some (Value v) ->
         if v = r.R.value then loop rest else Some (r.R.channel, "changed", (r.R.key, r.R.value, v)))
  in
  loop (p.R.start_tables @ p.R.reads)

let rec decide ~sentences ~closer =
  let r = decide_once ~sentences ~closer in
  (* A replay-only compile never stops the recorder, so its digest caches
     would grow for the whole file (review P3Deep F7). A compile that also
     records keeps them: they are the recorder's. *)
  if not (Proof_recorder.active ()) then Proof_recorder.reset_caches ();
  r

and decide_once ~sentences ~closer =
  match !state with
  | None | Some { f_candidate = None; _ } | Some { f_refused = Some _; _ } -> None
  | Some ({ f_candidate = Some { c_proof = p; c_offset; c_provided = at_start }; _ } as st) ->
    let name = p.R.name in
    st.f_candidate <- None;
    (* A process-wide fence this process tripped (a stale Rocqlib cache, a
       closure a plugin installed over Rocq's own) stays tripped: from then
       on the proofs depend on state that no recorded read sees, so none is
       replayed for the rest of the process, whatever its record holds
       (Proof_recorder.fence_tripped). It is checked here, right before a
       stored term would be used, so a trip anywhere before the closer
       counts. *)
    let tripped =
      match toolchain_fence () with
      | Some _ as t -> t
      | None -> Proof_recorder.fence_tripped ()
    in
    match tripped with
    | Some (reason, detail) ->
      if counts.fence = None then counts.fence <- Some (reason ^ ": " ^ detail);
      counts.m_ineligible <- counts.m_ineligible + 1;
      outcome name "ineligible" None;
      None
    | None ->
    (* The closer is part of key item 1: a registered [Qed] is never an
       [Admitted] or a [Defined] now (GRADE's review, case V5). *)
    if closer <> p.R.closer || (closer <> "Qed" && closer <> "Save") then (miss_key name; None)
    else if R.digest_value sentences <> p.R.sentences then (miss_key name; None)
    else
      match p.R.replay with
      | None -> miss_key name; None
      | Some blob ->
        if not (!precheck blob) then (miss_key name; None)
        else
          let install_miss () =
            match !install_check blob with
            | r -> r
            | exception e when CErrors.noncritical e -> Some ("stored_term", "unknown")
          in
          match first_read_mismatch p ~at_start with
          | Some (channel, why, detail) -> Hashtbl.replace miss_detail name detail; miss_read name channel why; None
          | None ->
          match install_miss () with
          | Some (channel, why) -> miss_read name channel why; None
          | None ->
            counts.n_hits <- counts.n_hits + 1;
            if !first_hit = None then first_hit := Some c_offset;
            outcome name "hit" None;
            Queue.iter (fun f -> f (p.R.start_tables @ p.R.reads)) hit_hooks;
            counts.registered <- counts.registered +. p.R.wall_s;
            (match !clock with
             | Some (ratio, _) -> counts.charged <- counts.charged +. (ratio *. p.R.wall_s)
             | None -> ());
            Some blob

let channel_misses () =
  List.sort (fun (_, a) (_, b) -> compare b a) (List.of_seq (Hashtbl.to_seq channel_miss))

(* {6 The summary} *)

(* The summary's strings are proof names, channel names and fixed reasons.
   A name can hold anything a Rocq identifier can, so quote properly. *)
let quote s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c ->
       match c with
       | '"' -> Buffer.add_string b "\\\""
       | '\\' -> Buffer.add_string b "\\\\"
       | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
       | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let summary ~killed =
  let elapsed = match !state with Some st -> Unix.gettimeofday () -. st.f_wall0 | None -> 0. in
  let channels =
    String.concat "," (List.map (fun (c, n) -> Printf.sprintf "[%s,%d]" (quote c) n) (channel_misses ()))
  in
  let outcomes =
    String.concat ","
      (List.rev_map
         (fun (name, kind, channel) ->
            match channel with
            | None -> Printf.sprintf "{\"name\":%s,\"outcome\":%s}" (quote name) (quote kind)
            | Some (c, why) ->
              let detail = match Hashtbl.find_opt miss_detail name with
                | None -> ""
                | Some (key, was, now) ->
                  (* Cut at a character boundary: the summary is JSON, and half a
                     UTF-8 sequence makes the whole file unreadable. *)
                  let cut s =
                    if String.length s <= 300 then s
                    else
                      let k = ref 300 in
                      while !k > 0 && Char.code s.[!k] land 0xC0 = 0x80 do decr k done;
                      String.sub s 0 !k ^ "..."
                  in
                  let opt = function None -> "null" | Some v -> quote (cut v) in
                  Printf.sprintf ",\"key\":%s,\"recorded\":%s,\"now\":%s" (quote (cut key)) (opt was) (opt now)
              in
              Printf.sprintf "{\"name\":%s,\"outcome\":%s,\"channel\":%s,\"why\":%s%s}"
                (quote name) (quote kind) (quote c) (quote why) detail)
         counts.outcomes)
  in
  let requires =
    String.concat ","
      (List.rev_map (fun (off, loaded) -> Printf.sprintf "[%d,%b]" off loaded) !requires_seen)
  in
  Printf.sprintf
    "{\"version\":1,\"proofs\":%d,\"hits\":%d,\
     \"misses\":{\"key\":%d,\"read\":%d,\"ineligible\":%d,\"missing_record\":%d},\
     \"refused\":%s,\"refused_detail\":%s,\"charged_s\":%.6f,\"registered_s\":%.6f,\"elapsed_s\":%.6f,\
     \"killed\":%s,\"fence\":%s,\"channel_misses\":[%s],\"requires\":[%s],\"outcomes\":[%s]}\n"
    counts.n_proofs counts.n_hits counts.m_key counts.m_read counts.m_ineligible counts.m_missing
    (match refused () with None -> "null" | Some r -> quote r)
    (match !state with Some { f_refused_detail = Some d; _ } -> quote d | _ -> "null")
    counts.charged counts.registered elapsed
    (if killed then "true" else "false")
    (match counts.fence with None -> "null" | Some f -> quote f)
    channels requires outcomes

(* {6 The stored term} *)

(* The term the closer about to run declares in place of the proof's own.
   The declaration takes it; the caller clears it, so a closer that took
   another path leaves none behind. *)
let pending : string option ref = ref None

let set_pending v = pending := v

let take_pending () = let v = !pending in pending := None; v
