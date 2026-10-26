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

type source =
  | Record_file of string
  | Record_dir of string

type options = {
  o_source : source;
  o_ratio : float;
  o_budget : float option;
  o_peak_limit_kb : int option;
  o_digest : string option;  (** the record's SHA-256, from the registration's manifest *)
}

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

(* A process-wide counter a proof's tactics move. A replayed proof's
   tactics do not run, so the counter would stay where it was and the
   proofs after it would make different fresh names (a hint's [_<n>], an
   SSR abstract variable). So replay reads each counter where the proof
   starts and, after the declaration, puts it at start plus the advance
   the registration recorded. The declaration's own advance is overwritten
   rather than added, which is what stock leaves behind.

   The universe and sort counters are not registered here: the stored term
   carries them ([rb_univ_end] in [Declare]). A counter nothing registers
   is one replay cannot move, so a proof that moved it is refused. *)
let counter_io : (string, (unit -> int) * (int -> unit)) Hashtbl.t = Hashtbl.create 8

let register_counter name ~get ~set = Hashtbl.replace counter_io name (get, set)

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

let can_advance name = Hashtbl.mem counter_io name || Hashtbl.mem summary_counters name

(* The counters of the proof being replayed: where each stood when the
   proof opened, and the advance its record holds. The start is taken at
   the proof's start, as the registration counted its advance from there;
   taken at the closer it would already hold what opening the proof
   spent. *)
let counter_starts () =
  Hashtbl.fold (fun name (get, set) acc -> (name, get (), set) :: acc) counter_io []

let pending_counters : (int * int * (int -> unit)) list ref = ref []

let take_counters ~starts ~recorded =
  pending_counters :=
    List.filter_map
      (fun (name, start, set) ->
         match List.assoc_opt name recorded with
         | Some n -> Some (start, n, set)
         | None -> None)
      starts

let apply_counters () =
  List.iter (fun (start, n, set) -> set (start + n)) !pending_counters;
  pending_counters := []

(* The layer that made a stored term says, at the closer, whether this
   compile can use it. It is never a reason to use one. *)
let precheck : (string -> bool) ref = ref (fun _ -> false)

let register_precheck f = precheck := f

let provided () =
  let tbl = Hashtbl.create 32 in
  let channels = Hashtbl.create 16 in
  Queue.iter
    (fun f ->
       List.iter
         (fun (r : R.read) ->
            Hashtbl.replace tbl (r.R.channel, r.R.key) r.R.value;
            Hashtbl.replace channels r.R.channel ())
         (f ()))
    providers;
  (tbl, channels)

type candidate = {
  c_name : string;
  c_proof : R.proof;
  c_provided : (string * string, string option) Hashtbl.t * (string, unit) Hashtbl.t;
      (** the provided channels, read where the record read them: at the
          proof's start, not at its closer *)
  c_counters : (string * int * (int -> unit)) list;  (** each counter at the proof's start *)
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
  f_refused_detail : string option;  (** for ["rebind"]: the command and its line *)
  mutable f_candidate : candidate option;
}

let options : options option ref = ref None
let state : file_state option ref = ref None

let counts = {
  n_proofs = 0; n_hits = 0; m_key = 0; m_read = 0; m_ineligible = 0; m_missing = 0;
  charged = 0.; registered = 0.; outcomes = []; fence = None;
}

let channel_miss : (string, int) Hashtbl.t = Hashtbl.create 16

let configure ~source ~ratio ~budget ~peak_limit_kb ~digest =
  options :=
    Some { o_source = source; o_ratio = ratio; o_budget = budget; o_peak_limit_kb = peak_limit_kb;
           o_digest = digest }

let configured () = !options <> None

let enabled () = match !state with Some { f_refused = None; _ } -> true | _ -> false

let refused () = match !state with Some st -> st.f_refused | None -> None

(* Where this library's record is. A file source is the record itself; a
   directory holds one record per library. Three places are tried: the
   library's dotted logical name, that name with its dots turned into
   slashes, and the path of the [.vo] this compile writes, relative to the
   working directory. The last is the layout of a registration tree, and
   of the engine's per-file staging. *)
let record_of_vo = ref None

let set_vo_path vo = record_of_vo := Some (Filename.remove_extension vo ^ ".proof-record.jsonl")

let record_path ~library = function
  | Record_file f -> Some f
  | Record_dir dir ->
    let places =
      [ library ^ ".proof-record.jsonl";
        String.concat Filename.dir_sep (String.split_on_char '.' library) ^ ".proof-record.jsonl" ]
      @ (match !record_of_vo with
          | Some p when Filename.is_relative p
                        && not (List.mem Filename.parent_dir_name (String.split_on_char '/' p)) -> [ p ]
          | Some _ | None -> [])
    in
    List.find_opt Sys.file_exists (List.map (Filename.concat dir) places)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(* A compile that ran under a limit which can end an allocation before the
   cgroup kill is not replayed, in either direction: under such a limit a
   proof can fail where the other run's did not, and a stored term would
   hide it (BET-84 spec, "When a stored term is used"). A value that could
   not be read ("unknown", a sandbox that masks /proc/sys) refuses too: a
   guard that cannot see is not a guard (review P3Deep F6). *)
let overcommit_refuses v = v <> "0" && v <> "1"

let limits_refusal (h : R.header) =
  if h.R.rlimit_as <> "unlimited" || h.R.rlimit_data <> "unlimited" then Some "rlimit"
  else if overcommit_refuses h.R.overcommit_memory then Some "overcommit"
  else None

let own_limits_refusal () =
  if Proof_limits.rlimit "Max address space" <> "unlimited"
     || Proof_limits.rlimit "Max data size" <> "unlimited"
  then Some "rlimit"
  else if overcommit_refuses (Proof_limits.overcommit_memory ()) then Some "overcommit"
  else None

(* The record is a TRUSTED input, at the same tier as the binary: its
   stored terms are read back with [Marshal.from_string], which is not
   memory-safe on chosen bytes, and a stored term's declared type comes
   from it. So the record is used only when it is bound to this compile
   (reviews P3Deep F1, P3Bugs):
   - its bytes hash (SHA-256) to an expected digest, which is mandatory:
     [-proof-replay-digest], which the grading engine takes from the
     registration's root-owned manifest, or with [-proof-replay-dir] a
     [<record>.sha256] file beside each record, as unwritable as it;
   - nobody but its owner can write it, and the compiling user cannot
     write it at all: write permission is what would let a principal that
     runs as that user replace a record between the hash and the read. For
     root, which [access] always lets write, the mode bits decide;
   - its header names the library this compile builds, and it is a
     record format this binary writes ([tables_at_start]). *)
let writable_by_us path =
  match Unix.stat path with
  | exception Unix.Unix_error _ -> true
  | st ->
    st.Unix.st_perm land 0o022 <> 0
    || (if Unix.getuid () = 0 then st.Unix.st_perm land 0o222 <> 0
        else (try Unix.access path [ Unix.W_OK ]; true with Unix.Unix_error _ -> false))

(* The record's expected SHA-256 is MANDATORY (reviews P3Deep F1, P3Bugs):
   [-proof-replay FILE] requires [-proof-replay-digest]; with
   [-proof-replay-dir], each record's digest is read from
   [<record>.sha256] beside it, which must be as unwritable as the record.
   A record with no digest to check it against is refused. *)
let expected_digest path =
  match !options with
  | Some { o_digest = Some d; _ } -> Some d
  | Some { o_source = Record_dir _; _ } ->
    let side = path ^ ".sha256" in
    if not (Sys.file_exists side) || writable_by_us side then None
    else
      (match read_file side with
       | s when String.length s >= 64 -> Some (String.sub s 0 64)
       | _ -> None
       | exception Sys_error _ -> None)
  | Some { o_source = Record_file _; o_digest = None; _ } | None -> None

let binding_refusal ~library ~path ~bytes (h : R.header) =
  match expected_digest path with
  | None -> Some "digest"
  | Some d when not (String.equal (String.lowercase_ascii d) (Proof_sha256.digest_hex bytes)) ->
    Some "digest"
  | Some _ ->
    if writable_by_us path then Some "writable"
    else if not (String.equal h.R.library library) then Some "library"
    else if not h.R.tables_at_start then Some "format"
    else None

(* A file whose registration needed more memory than the share this grade
   can give one compile runs without replay: all the build's jobs share one
   cgroup, so stock's own memory failures depend on what else runs. *)
let peak_refusal opts (t : R.trailer) =
  match opts.o_peak_limit_kb with
  | Some limit when t.R.peak_rss_kb > limit -> Some "memory"
  | _ -> None

(* A record another toolchain wrote is refused for the whole file, before
   any proof of it is declared: an object built by one Rocq can fail coqchk
   under another (the guard fix of 2026-10-25 made two let-based shapes
   fail that passed before it). The per-proof key holds the same items, so
   this is a second layer that names the reason once, in the summary.

   The load order is compared by the libraries' names, as the key compares
   it: a required library the agent edited has another digest, and a file
   that requires it is exactly the file replay exists for. Its contents
   reach a proof only through the reads, which are checked one by one. The
   warnings are not compared here: they are a per-proof key item, and a
   file can change them with [Set Warnings]. *)
let toolchain_refusal ~(now : R.toolchain) (h : R.header) =
  let r = h.R.toolchain in
  if r.R.binary <> now.R.binary || r.R.plugins <> now.R.plugins
     || List.map fst r.R.load_order <> List.map fst now.R.load_order
     || r.R.safe_deps <> now.R.safe_deps || r.R.stack_limit <> now.R.stack_limit
  then Some "toolchain"
  else None

(* A replayed proof's tactics do not run, so the process-wide caches they
   would have filled stay empty (about 120 [lazy] values hold a [lib_ref]
   answer the first time they are forced, and never ask again), and a closure
   they would have installed is not installed. A later command that rebinds
   a Rocqlib name, or loads code, then makes a later proof see what stock
   would not have seen: stock's lazy holds the old answer, replay's is forced
   after the rebinding (Claude review of c2190e74e0, P1: a [congruence] proof
   replayed, then [Register myeq as core.eq.type.], then a [congruence] proof
   that fails under replay and passes in stock). The trip of a fence comes too
   late to help: the proofs already replayed cannot be taken back.

   So the whole file runs without replay when, after its first [Qed] or
   [Save] (no proof can be replayed before it), its text holds a command that
   can rebind a Rocqlib name or load code. A [Register] object is applied
   when it is declared, when its library or module is loaded (a superglobal
   object, Libobject.object_with_locality), when its module is opened (an
   export one), when a module is sealed by a signature that holds one, and a
   section's end takes back what was applied inside it. So, after the first
   closer: [Register]; [Require] (a library brings its own [Register]
   objects and plugins, which the text does not show); [Load]; [Declare] (ML
   Module, Module); [Import]; [Export]; [Include]; any [Module]; and an [End]
   that closes a module (a sealed one applies its signature's objects there)
   or a section inside which one of those commands appeared, before or after
   the first closer (Claude delta review of 7b2a60f377, P1-2 to P1-4).
   Decided from the source text, before any proof is replayed. The scan
   skips nested comments and strings, and splits words as Rocq's lexer does:
   a word starts with a letter or [_], so [1Register] is the number [1] and
   the word [Register] (P1-1). It is meant to err toward refusing (a keyword
   inside a quotation or a notation's text refuses too); a command that a
   [Load]ed file, a plugin or a notation builds is covered because [Load],
   [Declare] and [Require] refuse. Main's ruling, 2026-10-26 18:10Z, asked
   for [Register], [Declare ML Module], a plugin-loading [Require] and
   [Load]; the rest are the other ways a [Register] object is applied. *)
let late_words = [ "Register"; "Require"; "Load"; "Declare"; "Import"; "Export"; "Include"; "Module" ]

let scan_late_rebind text =
  let n = String.length text in
  let line = ref 1 and i = ref 0 in
  let closed = ref false in
  (* One frame per open [Section] or [Module]: whether its [End] can change
     what a Rocqlib name answers. A module's always can; a section's can when
     a late word appeared inside it, at any depth. Only a sentence's command
     word opens or closes one: [Print Section S.] opens nothing, [Fail End S.]
     closes nothing (Claude delta review of 2daae0ed39, P1-2). *)
  let frames : bool ref list ref = ref [] in
  let result = ref None in
  let is_letter c = match c with
    | 'a'..'z' | 'A'..'Z' -> true
    | c -> Char.code c >= 128
  in
  let is_run c = is_letter c || (match c with '0'..'9' | '_' | '\'' -> true | _ -> false) in
  let step () = if text.[!i] = '\n' then incr line; incr i in
  let skip_string () =
    (* [""] inside a string is a quote *)
    incr i;
    let fin = ref false in
    while not !fin && !i < n do
      if text.[!i] = '"' then
        if !i + 1 < n && text.[!i + 1] = '"' then i := !i + 2 else (incr i; fin := true)
      else step ()
    done
  in
  let skip_comment () =
    i := !i + 2;
    let depth = ref 1 in
    while !depth > 0 && !i < n do
      if text.[!i] = '(' && !i + 1 < n && text.[!i + 1] = '*' then (incr depth; i := !i + 2)
      else if text.[!i] = '*' && !i + 1 < n && text.[!i + 1] = ')' then (decr depth; i := !i + 2)
      else if text.[!i] = '"' then skip_string ()
      else step ()
    done
  in
  (* Whether the sentence from here to its terminating dot holds [:=],
     comments and strings skipped. The position and line are restored. *)
  let sentence_assigns () =
    let i0 = !i and l0 = !line in
    let res = ref None in
    while !res = None && !i < n do
      let c = text.[!i] in
      if c = '(' && !i + 1 < n && text.[!i + 1] = '*' then skip_comment ()
      else if c = '"' then skip_string ()
      else if c = ':' && !i + 1 < n && text.[!i + 1] = '=' then res := Some true
      else if c = '.' && (!i + 1 >= n || String.contains " \n\t\r" text.[!i + 1]) then res := Some false
      else step ()
    done;
    i := i0; line := l0;
    !res = Some true
  in
  let found w = result := Some (w, !line) in
  (* A late word is found wherever its letters end a run that is not part of
     a longer word: Rocq's lexer reads [1Register], [1_Register] and
     [0x1Register] as a number then [Register] (P1-1), so a late word counts
     when it starts the run or follows a digit, [_] or ['] in it. This also
     takes an identifier such as [x_Register] for the word, which only costs
     a replay. *)
  let late_in run =
    List.find_opt
      (fun k ->
         let lr = String.length run and lk = String.length k in
         lr >= lk && String.equal (String.sub run (lr - lk) lk) k
         && (lr = lk || not (is_letter run.[lr - lk - 1])))
      late_words
  in
  let prefixes =
    [ "Local"; "Global"; "Time"; "Timeout"; "Redirect"; "Instructions"; "Profile"; "Polymorphic";
      "Monomorphic"; "Cumulative"; "NonCumulative"; "Private"; "Program"; "Fail"; "Succeed" ] in
  let at_start = ref true and under_fail = ref false and cmd_module = ref false in
  while !result = None && !i < n do
    let c = text.[!i] in
    if c = '(' && !i + 1 < n && text.[!i + 1] = '*' then skip_comment ()
    else if c = '"' then (skip_string ())
    else if c = '#' && !i + 1 < n && text.[!i + 1] = '[' then begin
      (* an attribute: the command word is still to come *)
      while !i < n && text.[!i] <> ']' do
        if text.[!i] = '"' then skip_string () else step ()
      done;
      if !i < n then incr i
    end
    else if is_run c then begin
      let j = ref !i in
      while !j < n && is_run text.[!j] do incr j done;
      let run = String.sub text !i (!j - !i) in
      let lead_letter = is_letter c in
      (match late_in run with
       | Some w ->
         List.iter (fun f -> f := true) !frames;
         if !closed then found w
       | None -> ());
      if !result = None then begin
        if !at_start && lead_letter && List.mem run prefixes then begin
          if String.equal run "Fail" || String.equal run "Succeed" then under_fail := true
        end
        else if !at_start && not lead_letter then ()  (* [Timeout 5] *)
        else if !at_start then begin
          at_start := false;
          if not !under_fail then begin
            if String.equal run "Module" then cmd_module := true
            else if String.equal run "Section" then frames := ref false :: !frames
            else if String.equal run "End" then begin
              match !frames with
              | f :: rest -> frames := rest; if !closed && !f then found "End (of a module, or of a section that loads or imports)"
              | [] -> if !closed then found "End"
            end
          end
        end
        else if !cmd_module then begin
          (* [Module Type T], [Module Export M]: the name comes later *)
          if not (List.mem run [ "Type"; "Import"; "Export" ]) then begin
            cmd_module := false;
            i := !j;
            if not (sentence_assigns ()) then frames := ref true :: !frames
          end
        end;
        if String.equal run "Qed" || String.equal run "Save" then closed := true
      end;
      i := !j
    end
    else begin
      (* A sentence ends at a dot followed by a space or the end; a bullet or
         a brace before a command leaves it at the start. *)
      if c = '.' && (!i + 1 >= n || String.contains " \n\t\r" text.[!i + 1]) then begin
        at_start := true; under_fail := false; cmd_module := false
      end;
      step ()
    end
  done;
  !result

(* A plugin outside the audited set (the plugins this tree builds) can add
   commands the source scan cannot read (one could rebind a Rocqlib name after
   a replayed proof), and closures no read sees. Loading one after the first
   closer is a [Require] or [Declare] the scan refuses; loading one before is
   caught here: while such a plugin is loaded, no proof is replayed (Claude
   delta review of 2daae0ed39, P2-1). The audit is the ltac plugin's list of
   audited packages (Tacinterp.audited_ml_tactic_plugins); until it registers,
   no plugin counts as audited. *)
let plugin_audit : (string -> bool) ref = ref (fun _ -> false)

let register_plugin_audit f = plugin_audit := f

let toolchain_now : (unit -> R.toolchain) option ref = ref None

let unaudited_plugin () =
  match !toolchain_now with
  | None -> None
  | Some tc -> List.find_opt (fun (name, _) -> not (!plugin_audit name)) (tc ()).R.plugins

let source_rebind = function
  | None -> None
  | Some path ->
    match read_file path with
    | text -> scan_late_rebind text
    | exception (Sys_error _ | End_of_file) -> Some ("an unreadable source", 0)

let start ~library ~source ~toolchain =
  match !options with
  | None -> ()
  | Some opts ->
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
    Hashtbl.reset proof_provided;
    pending_counters := [];
    let index = Hashtbl.create 256 in
    let refusal =
      match record_path ~library opts.o_source with
      | None -> Some "bad_record"
      | Some path ->
        let bytes = read_file path in
        (match R.parse_string bytes with
         | exception _ -> Some "bad_record"
         | file ->
           let refusal =
             match binding_refusal ~library ~path ~bytes file.R.header with
             | Some r -> Some r
             | None ->
             match toolchain_refusal ~now:(toolchain ()) file.R.header with
             | Some r -> Some r
             | None ->
             match limits_refusal file.R.header with
             | Some r -> Some r
             | None ->
               (match own_limits_refusal () with
                | Some r -> Some r
                | None -> peak_refusal opts file.R.trailer)
           in
           if refusal = None then
             List.iter (fun (p : R.proof) -> Hashtbl.replace index p.R.name p) file.R.proofs;
           refusal)
    in
    (* The registration ran its process-wide cache fences from its start
       ([Proof_recorder.start]); a replay that does not run them would let
       a dirty history here match the clean one recorded there. From here
       on they run at each decision ({!decide}). *)
    let refusal, refused_detail =
      match refusal with
      | Some _ -> refusal, None
      | None ->
        match source_rebind source with
        | Some (cmd, line) -> Some "rebind", Some (Printf.sprintf "%s at line %d" cmd line)
        | None -> None, None
    in
    if refusal = None then Proof_recorder.start_tracking ();
    toolchain_now := Some toolchain;
    state := Some { f_index = index; f_wall0 = process_start; f_refused = refusal;
                    f_refused_detail = refused_detail; f_candidate = None }

let check_budget () =
  match !options, !state with
  | Some { o_budget = Some budget; _ }, Some st ->
    if Unix.gettimeofday () -. st.f_wall0 +. counts.charged >= budget then raise Budget_exhausted
  | _ -> ()

(* What is left of the budget once the charge for the replayed proofs is
   taken off. A sentence runs under this as a timeout, so a proof that runs
   long is stopped inside it, where stock's own timeout stops it, and not
   only at the next sentence boundary. *)
let remaining_budget () =
  match !options, !state with
  | Some { o_budget = Some budget; _ }, Some st ->
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

(* Run on each hit with the replayed proof's reads: the owner of a
   process-wide cache can treat what the proof read as looked up (Rocqlib
   marks its [lib_ref] keys observed, so a later rebinding of one trips its
   fence and no later proof is replayed). It stops later replays only; the
   whole-file refusal above is what keeps later tactics seeing what stock
   sees. *)
let hit_hooks : (R.read list -> unit) Queue.t = Queue.create ()

let register_hit_hook f = Queue.add f hit_hooks


let candidate_open () = match !state with Some { f_candidate = Some _; _ } -> true | _ -> false

(* The proof ran its tactics without a decision: its sentences were not the
   ones the record holds (a command inside the proof, a parse that stopped
   the buffering). That is key item 1. *)
let abandon () =
  match !state with
  | Some ({ f_candidate = Some c; _ } as st) -> st.f_candidate <- None; miss_key c.c_name
  | Some _ | None -> ()

(* A write the declaration of the stored term does not make by itself: a
   warning the proof raised, which [Set Warnings "+..."] can turn into an
   error, and a counter that no [register_counter] can move. The
   declaration makes the rest — the levels and constraints, the constraint
   sources, and the schemes, which travel with the term's side effects.

   The universe and sort counters are not here: the stored term carries
   them, and the precheck compares them. Every other registered counter is
   moved at the closer by [advance_counters]. *)
let unreplayable_writes (p : R.proof) =
  p.R.writes.R.warnings_raised <> []
  || List.exists
       (fun (name, n) ->
          n > 0 && name <> "univ_level" && name <> "sort_quality" && not (can_advance name))
       p.R.writes.R.counters

let open_proof ~name ~statement ~position ~toolchain_key =
  match !state with
  | None | Some { f_refused = Some _; _ } -> ()
  | Some st ->
    st.f_candidate <- None;
    Hashtbl.reset proof_provided;
    counts.n_proofs <- counts.n_proofs + 1;
    (match Hashtbl.find_opt st.f_index name with
     | None -> counts.m_missing <- counts.m_missing + 1; outcome name "missing_record" None
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
           Some { c_name = name; c_proof = p; c_provided = provided (); c_counters = counter_starts () })

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
(* Why a read missed: its channel has no evaluator in this Rocq
   (["no_evaluator"]), the evaluator could not answer (["unknown"]), or the
   value now is another one (["changed"]). *)
let first_read_mismatch (p : R.proof) ~at_start =
  let now (r : R.read) =
    let table, _channels = at_start in
    match Hashtbl.find_opt proof_provided (r.R.channel, r.R.key) with
    | Some v -> Some (Value v)
    | None ->
      match Hashtbl.find_opt table (r.R.channel, r.R.key) with
      | Some v -> Some (Value v)
      | None ->
        match Hashtbl.find_opt evaluators r.R.channel with
        | None -> None
        | Some f -> Some (match f r.R.key with v -> v | exception _ -> Unknown)
  in
  let rec loop = function
    | [] -> None
    | (r : R.read) :: rest ->
      (match now r with
       | None -> Some (r.R.channel, "no_evaluator")
       | Some Unknown -> Some (r.R.channel, "unknown")
       | Some (Value v) -> if v = r.R.value then loop rest else Some (r.R.channel, "changed"))
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
  | Some ({ f_candidate = Some { c_name = name; c_proof = p; c_provided = at_start; c_counters = starts };
            _ } as st) ->
    st.f_candidate <- None;
    (* A process-wide fence this process tripped (a stale Rocqlib cache, a
       closure a plugin installed over Rocq's own) stays tripped: from then
       on the proofs depend on state that no recorded read sees, so none is
       replayed for the rest of the process, whatever its record holds
       (Proof_recorder.fence_tripped). It is checked here, right before a
       stored term would be used, so a trip anywhere before the closer
       counts. *)
    let tripped =
      match unaudited_plugin () with
      | Some (name, _) -> Some ("unaudited_plugin", name)
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
          match first_read_mismatch p ~at_start with
          | Some (channel, why) -> miss_read name channel why; None
          | None ->
            counts.n_hits <- counts.n_hits + 1;
            outcome name "hit" None;
            Queue.iter (fun f -> f (p.R.start_tables @ p.R.reads)) hit_hooks;
            take_counters ~starts ~recorded:p.R.writes.R.counters;
            counts.registered <- counts.registered +. p.R.wall_s;
            (match !options with
             | Some opts -> counts.charged <- counts.charged +. (opts.o_ratio *. p.R.wall_s)
             | None -> ());
            Some blob

let channel_misses () =
  List.sort (fun (_, a) (_, b) -> compare b a) (List.of_seq (Hashtbl.to_seq channel_miss))

(* {6 The summary} *)

let summary_path_of_vo vo = Filename.remove_extension vo ^ ".proof-replay.json"

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
              Printf.sprintf "{\"name\":%s,\"outcome\":%s,\"channel\":%s,\"why\":%s}"
                (quote name) (quote kind) (quote c) (quote why))
         counts.outcomes)
  in
  Printf.sprintf
    "{\"version\":1,\"proofs\":%d,\"hits\":%d,\
     \"misses\":{\"key\":%d,\"read\":%d,\"ineligible\":%d,\"missing_record\":%d},\
     \"refused\":%s,\"refused_detail\":%s,\"charged_s\":%.6f,\"registered_s\":%.6f,\"elapsed_s\":%.6f,\
     \"killed\":%s,\"fence\":%s,\"channel_misses\":[%s],\"outcomes\":[%s]}\n"
    counts.n_proofs counts.n_hits counts.m_key counts.m_read counts.m_ineligible counts.m_missing
    (match refused () with None -> "null" | Some r -> quote r)
    (match !state with Some { f_refused_detail = Some d; _ } -> quote d | _ -> "null")
    counts.charged counts.registered elapsed
    (if killed then "true" else "false")
    (match counts.fence with None -> "null" | Some f -> quote f)
    channels outcomes

let write ~killed path =
  if configured () then begin
    let oc = open_out_bin path in
    Fun.protect ~finally:(fun () -> close_out_noerr oc) (fun () -> output_string oc (summary ~killed))
  end

let write_summary path = write ~killed:false path
let killed_summary path = write ~killed:true path

(* {6 The stored term} *)

(* The term the closer about to run declares in place of the proof's own.
   The declaration takes it; the caller clears it, so a closer that took
   another path leaves none behind. *)
let pending : string option ref = ref None

let set_pending v = pending := v

let take_pending () = let v = !pending in pending := None; v

let b64_alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

let encode_blob s =
  let n = String.length s in
  let b = Buffer.create (4 * ((n + 2) / 3)) in
  let byte i = if i < n then Char.code s.[i] else 0 in
  let rec loop i =
    if i < n then begin
      let x = (byte i lsl 16) lor (byte (i + 1) lsl 8) lor byte (i + 2) in
      Buffer.add_char b b64_alphabet.[(x lsr 18) land 63];
      Buffer.add_char b b64_alphabet.[(x lsr 12) land 63];
      Buffer.add_char b (if i + 1 < n then b64_alphabet.[(x lsr 6) land 63] else '=');
      Buffer.add_char b (if i + 2 < n then b64_alphabet.[x land 63] else '=');
      loop (i + 3)
    end
  in
  loop 0;
  Buffer.contents b

let b64_value =
  lazy
    (let t = Array.make 256 (-1) in
     String.iteri (fun i c -> t.(Char.code c) <- i) b64_alphabet;
     t)

let decode_blob s =
  let t = Lazy.force b64_value in
  let b = Buffer.create (3 * (String.length s / 4)) in
  let acc = ref 0 and bits = ref 0 in
  try
    String.iter
      (fun c ->
         if c <> '=' then begin
           let v = t.(Char.code c) in
           if v < 0 then raise Exit;
           acc := (!acc lsl 6) lor v;
           bits := !bits + 6;
           if !bits >= 8 then begin
             bits := !bits - 8;
             Buffer.add_char b (Char.chr ((!acc lsr !bits) land 0xff))
           end
         end)
      s;
    Some (Buffer.contents b)
  with Exit -> None
