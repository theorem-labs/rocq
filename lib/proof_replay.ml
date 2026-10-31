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

(* The last check, once every recorded read gave its value again: the layer
   that made the blob puts together what the declaration takes (the proof
   term the blob refers to, the universe state it rebuilds) and says whether
   it is the same as what the registration declared. A difference is a
   read miss, on the channel and for the reason it names. *)
let install_check : (string -> (string * string) option) ref = ref (fun _ -> Some ("stored_term", "unknown"))

let register_install_check f = install_check := f

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

(* A [Require] the source text spells out in full: its [From] prefix and
   its library names, as written ({!scan_late_commands}). *)
type require_text = { rq_from : string option; rq_names : string list }

(* A late command of the source text: its word's byte offset and, for a
   [Require] the text spells out in full, that [Require]. *)
type late_command = { lc_offset : int; lc_require : require_text option }

(* What a proof has to open after to replay: the last late command that is
   late whatever is loaded, and the [Require]s after it, last first, with
   their offsets. Each of those is late only while a library it names is
   not loaded ({!opens_before_late_command}). *)
type late_bound = { lb_last : int option; lb_requires : (int * require_text) list }

let no_late = { lb_last = None; lb_requires = [] }

type candidate = {
  c_name : string;
  c_proof : R.proof;
  c_offset : int;  (** where the proof's opening sentence starts *)
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
  f_refused_detail : string option;
      (** for ["rebind"], and for a file with a late command: the command and its line *)
  f_late : late_bound;
      (** the late commands, [Import] and [Export] counted: the bound once
          an export-locality registration is loaded *)
  f_late_no_imports : late_bound;
      (** the same, [Import] and [Export] not counted: the bound while no
          export-locality registration is loaded *)
  f_object : (string * string option) option;
      (** the registered [.vo] beside the record, and the SHA-256 of its
          opaque proofs the record's trailer holds *)
  mutable f_candidate : candidate option;
}

let options : options option ref = ref None
let state : file_state option ref = ref None

let counts = {
  n_proofs = 0; n_hits = 0; m_key = 0; m_read = 0; m_ineligible = 0; m_missing = 0;
  charged = 0.; registered = 0.; outcomes = []; fence = None;
}

let channel_miss : (string, int) Hashtbl.t = Hashtbl.create 16

(* For each proof that missed on a read: the read's key, its recorded value
   and its value now (absent when nothing answered), for the summary. *)
let miss_detail : (string, string * string option * string option) Hashtbl.t = Hashtbl.create 64

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
   after the rebinding (Claude review of c2190e74e0, P1). Which lazies are
   already forced when a proof starts is an input no read records: a proof
   whose registration found a lazy forced reads nothing, and the same proof
   in an edited file can be the one that forces it. So the hazard is decided
   by position, not per proof.

   A proof that opens after the last such command in the file meets a
   process whose state equals stock's: every proof before that command ran
   its tactics, and from there on no command rebinds a name or loads code,
   which is the state of a file with no such command at all. So those proofs
   may replay, and every proof that opens before the last such command runs
   (outcome [ineligible], channel ["rebind"]). The commands, after the
   file's first [Qed] or [Save] (no proof can be replayed before it), are:
   [Register]; [Require] (a library brings its own [Register] objects and
   plugins, which the text does not show), unless it loads nothing (below);
   [Load]; [Declare] (ML Module,
   Module); [Import] and [Export] once an export-locality registration is
   loaded (see {!scan_late_events}); [Include]; a [Module] that is not plain
   (sealed, a functor, a module type, a definition); and an [End] that closes
   such a module (a sealed one applies its signature's objects there), or a
   plain module or a section inside which one of those commands appeared
   (Claude delta review of 7b2a60f377, P1-2 to P1-4); and [Reset] ([Reset
   Initial] too), [Back] and [BackTo], which restore an earlier state: the
   Rocqlib table and every Summary go back, while a process-wide lazy that a
   proof before them forced does not (fourth soundness review, finding 3,
   fixture late_reset_congruence). Once one of these appears, the sections
   and modules the scan keeps track of no longer follow the restored state,
   so every later [End] counts too. Decided from the source
   text, before any proof is replayed, with two runtime conditions: the one
   on [Import], and the one on [Require].

   A [Require] is not late for a proof when every library it names is
   already loaded at the proof's opening. Such a [Require] loads nothing:
   [Library.intern_library] stops at a loaded library, whose dependencies
   are loaded too, so the closure it registers is empty; no object's load
   function runs (a SuperGlobal [Register] acts at load,
   [Libobject.object_with_locality]) and no plugin loads (an ML module acts
   at load, [Mltop.inMLModule]). Its [Import] or [Export] part is a late
   word of its own, under the [Import] rule. Nothing between the decision
   and the [Require] can unload a library or resolve a name otherwise
   without being late itself: only a [Require] loads a library, and one
   that loads any is late; the [Load], the [End] and the [Reset] that could
   undo a load are late; no command changes the load path (the [Add
   LoadPath] commands were removed: doc/sphinx/changes.rst, #17394); the
   decision resolves the names with the [Require]'s own function
   ([Synterp.require_locate]), and coqc keeps the directory listings it
   read ([System.trust_file_cache]). So the dependencies of the [Require]s
   between the proof and this one add nothing to what is loaded: if one of
   them loads a library, the proof runs anyway. A [Require] the text does
   not spell out in full ({!require_sentence}), or one with a name that
   does not resolve, stays late. A [Require] that loads a library after a
   replayed proof all the same stops the compile ({!note_require}).

   The scan skips nested comments and strings, and
   reads a number as Rocq's lexer reads one ([0-9][0-9_]*, a fraction and an
   exponent only when a digit follows, or [0x] and hexadecimal digits), so
   in [1Register], [0xaRegister] or [1End] the rest is a word (Claude delta
   reviews of 7b2a60f377 and a158379eb4, P1-1). It is meant to err toward a
   later position: a late word inside a quotation, a notation's text or an
   identifier ending in one ([x_Register]) counts too. A command a [Load]ed
   file builds is covered because [Load] counts; one a plugin adds is
   covered by the plugin audit below ({!unaudited_plugin}), not by this
   scan. *)
let restoring_words = [ "Reset"; "Back"; "BackTo" ]

let late_words =
  [ "Register"; "Require"; "Load"; "Declare"; "Import"; "Export"; "Include"; "Module" ] @ restoring_words

(* The [Require] sentence whose command word ([From] or [Require]) starts at
   byte [k], read as the grammar reads one (vernac/g_vernac.mlg): [From q]
   or nothing, [Require], [(safe)] or nothing, [Import] or [Export] with
   its import categories or nothing, one or more names each with an import
   filter or not, then the terminating dot. It gives the offset of the
   [Require] word, the [From] prefix and the names. A name is plain ASCII
   identifiers joined by dots with no blank around a dot, as the lexer
   joins a qualified name. Anything else gives [None], and the [Require]
   stays late: this reading can refuse a sentence Rocq accepts, and never
   takes other names from one it accepts. *)
let require_sentence text k =
  let ( let* ) = Option.bind in
  let n = String.length text in
  let i = ref k in
  let blank c = c = ' ' || c = '\n' || c = '\t' || c = '\r' in
  let at s = !i + String.length s <= n && String.equal (String.sub text !i (String.length s)) s in
  let skip_string () =
    incr i;
    let fin = ref false in
    while not !fin && !i < n do
      if text.[!i] <> '"' then incr i
      else if !i + 1 < n && text.[!i + 1] = '"' then i := !i + 2
      else (incr i; fin := true)
    done
  in
  let skip_comment () =
    i := !i + 2;
    let depth = ref 1 in
    while !depth > 0 && !i < n do
      if at "(*" then (incr depth; i := !i + 2)
      else if at "*)" then (decr depth; i := !i + 2)
      else if text.[!i] = '"' then skip_string ()
      else incr i
    done
  in
  let rec blanks () =
    if !i < n && blank text.[!i] then (incr i; blanks ())
    else if at "(*" then (skip_comment (); blanks ())
  in
  let ident_start c = match c with 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false in
  let ident_char c = ident_start c || (match c with '0'..'9' | '\'' -> true | _ -> false) in
  let ident () =
    if !i < n && ident_start text.[!i] then begin
      let s = !i in
      while !i < n && ident_char text.[!i] do incr i done;
      let id = String.sub text s (!i - s) in
      (* A byte above 127 goes on with a letter this reading does not take. *)
      if (!i < n && Char.code text.[!i] >= 128) || String.equal id "_" then None else Some id
    end
    else None
  in
  let qualid () =
    blanks ();
    let* id = ident () in
    let rec fields acc =
      if !i + 1 < n && text.[!i] = '.' && ident_start text.[!i + 1] then begin
        incr i;
        let* id = ident () in
        fields (acc ^ "." ^ id)
      end
      else Some acc
    in
    fields id
  in
  let word () = blanks (); ident () in
  let opens () = !i < n && text.[!i] = '(' && not (at "(*") in
  (* A group in parentheses: the import categories, or an import filter. *)
  let group () =
    let depth = ref 0 and ok = ref true and go = ref true in
    while !ok && !go do
      if !i >= n then ok := false
      else if at "(*" then skip_comment ()
      else match text.[!i] with
        | '(' -> incr depth; incr i
        | ')' -> decr depth; incr i; if !depth = 0 then go := false
        | '"' -> ok := false
        | '.' when !i + 1 >= n || blank text.[!i + 1] -> ok := false
        | _ -> incr i
    done;
    if !ok then Some () else None
  in
  let ends () = !i < n && text.[!i] = '.' && (!i + 1 >= n || blank text.[!i + 1]) in
  let* from =
    let s = !i in
    match word () with
    | Some "From" -> let* q = qualid () in Some (Some q)
    | Some "Require" -> i := s; Some None
    | _ -> None
  in
  blanks ();
  let at_require = !i in
  let* () = match ident () with Some "Require" -> Some () | _ -> None in
  blanks ();
  let* () =
    if not (opens ()) then Some ()
    else begin
      incr i;
      match word () with
      | Some "safe" -> blanks (); if !i < n && text.[!i] = ')' then (incr i; Some ()) else None
      | _ -> None
    end
  in
  let* () =
    let s = !i in
    match word () with
    | Some ("Import" | "Export") ->
      blanks ();
      if !i < n && text.[!i] = '-' then (incr i; blanks (); if opens () then group () else None)
      else if opens () then group ()
      else Some ()
    | _ -> i := s; Some ()
  in
  let rec names acc =
    blanks ();
    if ends () then (if acc = [] then None else Some (List.rev acc))
    else
      let* q = qualid () in
      blanks ();
      let* () = if opens () then group () else Some () in
      names (q :: acc)
  in
  let* names = names [] in
  Some (at_require, { rq_from = from; rq_names = names })

(* The first late command with its line, and every late command, last
   first. With [~imports_late:false], [Import] and [Export] are not late
   words: opening a module runs only its objects' open functions, which load
   no code (an ML module acts at load: [Mltop.inMLModule]) and change a
   Rocqlib answer only through an export-locality [Register]
   ([Libobject.object_with_locality]: SuperGlobal acts at load, Export at
   open). The caller uses that scan only while no export-locality
   registration has been loaded or declared ({!note_export_register}).

   A plain module, [Module M.] or [Module Import M.] with no binder, no
   signature and no [:=], is not late by itself, and its [End] is late only
   when a late word appeared inside it: ending it loads again only the
   objects declared in its body, and a body with no late word declares no
   Rocqlib registration and loads no code. A sealed module, a functor, a
   module type and a module definition stay late, and their [End] too.

   A [Require] that is the command word of its sentence, or follows the
   sentence's [From q], carries what it names when {!require_sentence}
   reads it. It still marks the frames it is in: the [End] of one stays
   late. *)
let scan_late_commands ?(imports_late = true) text =
  let late_words =
    if imports_late then late_words
    else List.filter (fun w -> w <> "Import" && w <> "Export") late_words
  in
  let n = String.length text in
  let line = ref 1 and i = ref 0 in
  let closed = ref false in
  (* One frame per open [Section] or [Module]: whether its [End] can change
     what a Rocqlib name answers. A non-plain module's always can; a plain
     module's and a section's can when a late word appeared inside it, at any
     depth. Only a sentence's command word opens or closes one: [Print
     Section S.] opens nothing, [Fail End S.] closes nothing (Claude delta
     review of 2daae0ed39, P1-2). *)
  let frames : bool ref list ref = ref [] in
  (* A [Reset], [Back] or [BackTo] has appeared: the frames no longer follow
     the restored sections and modules. *)
  let restored = ref false in
  let result = ref None and commands = ref [] in
  (* The offset of this sentence's command word when that word is [From]. *)
  let from_at = ref None in
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
  (* Whether the sentence from [j], just after its command word [Module], is
     [Import] or [Export] at most, then one identifier, then the terminating
     dot: a plain module. Comments are skipped; anything else (a binder, a
     signature, [:=], [<:], [Type]) is not plain. The position and line are
     restored. *)
  let plain_module_after j =
    let i0 = !i and l0 = !line in
    i := j;
    let skip_blank () =
      let go = ref true in
      while !go && !i < n do
        let c = text.[!i] in
        if c = '(' && !i + 1 < n && text.[!i + 1] = '*' then skip_comment ()
        else if String.contains " \n\t\r" c then step ()
        else go := false
      done
    in
    let word () =
      skip_blank ();
      let k = !i in
      while !i < n && is_run text.[!i] do incr i done;
      String.sub text k (!i - k)
    in
    let w = word () in
    let name = if String.equal w "Import" || String.equal w "Export" then word () else w in
    skip_blank ();
    let plain =
      name <> "" && (is_letter name.[0] || name.[0] = '_') && not (String.equal name "Type")
      && !i < n && text.[!i] = '.' && (!i + 1 >= n || String.contains " \n\t\r" text.[!i + 1])
    in
    i := i0; line := l0;
    plain
  in
  let found ?require w =
    if !result = None then result := Some (w, !line);
    commands := { lc_offset = !i; lc_require = require } :: !commands
  in
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
  while !i < n do
    let c = text.[!i] in
    if c = '(' && !i + 1 < n && text.[!i + 1] = '*' then skip_comment ()
    else if c = '"' then (skip_string ())
    else if !at_start && c = '#' && !i + 1 < n && text.[!i + 1] = '[' then begin
      (* An attribute before the command word: skip to its matching ']',
         skipping comments and strings inside it, so a ']' in either does
         not end it (Claude review of 951eb445f9, P1-1). *)
      i := !i + 2;
      let depth = ref 1 in
      while !depth > 0 && !i < n do
        let d = text.[!i] in
        if d = '(' && !i + 1 < n && text.[!i + 1] = '*' then skip_comment ()
        else if d = '"' then skip_string ()
        else if d = '[' then (incr depth; incr i)
        else if d = ']' then (decr depth; incr i)
        else step ()
      done
    end
    else if c >= '0' && c <= '9' then begin
      (* A number, exactly as the lexer takes it; what follows is a new
         word. It does not move the command start: [Timeout 5 Register]. *)
      let is_dig ch = ch >= '0' && ch <= '9' in
      let is_hex ch = is_dig ch || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F') in
      let take p = while !i < n && (p text.[!i] || text.[!i] = '_') do incr i done in
      let hex = c = '0' && !i + 2 < n && (text.[!i + 1] = 'x' || text.[!i + 1] = 'X') && is_hex text.[!i + 2] in
      let digits = if hex then is_hex else is_dig in
      if hex then i := !i + 2;
      take digits;
      if !i + 1 < n && text.[!i] = '.' && digits text.[!i + 1] then (incr i; take digits);
      let expo = if hex then (fun ch -> ch = 'p' || ch = 'P') else (fun ch -> ch = 'e' || ch = 'E') in
      if !i < n && expo text.[!i] then begin
        let k = if !i + 1 < n && (text.[!i + 1] = '+' || text.[!i + 1] = '-') then !i + 2 else !i + 1 in
        if k < n && is_dig text.[k] then (i := k; take is_dig)
      end
    end
    else if is_run c then begin
      let j = ref !i in
      while !j < n && is_run text.[!j] do incr j done;
      let run = String.sub text !i (!j - !i) in
      let lead_letter = is_letter c in
      (* A component of a qualified identifier, [Module.module_contents] in
         an Ltac2 tactic or [M.Register], is part of one identifier token to
         Rocq's lexer, never a command keyword: the run is followed by a dot
         and an identifier's first character, or follows a dot that follows
         an identifier character. It is neither a late word nor a command
         word. The name after a [Module] command keeps the rule below. *)
      let qualified =
        not !cmd_module
        && ((!j + 1 < n && text.[!j] = '.' && (is_letter text.[!j + 1] || text.[!j + 1] = '_'))
            || (!i >= 2 && text.[!i - 1] = '.' && is_run text.[!i - 2]))
      in
      let plain_module =
        !at_start && not !under_fail && String.equal run "Module" && plain_module_after !j
      in
      if qualified then at_start := false
      else if plain_module then begin
        at_start := false;
        frames := ref false :: !frames
      end
      else begin
      (match late_in run with
       | Some w ->
         List.iter (fun f -> f := true) !frames;
         if List.mem w restoring_words then restored := true;
         if !closed then begin
           (* A [Require] as the command word, or after [From q]. *)
           let require =
             if not (String.equal run "Require") then None
             else
               let start = if !at_start then Some !i else !from_at in
               match Option.bind start (require_sentence text) with
               | Some (at, r) when at = !i -> Some r
               | _ -> None
           in
           found ?require w
         end
       | None -> ());
      begin
        if !at_start && lead_letter && List.mem run prefixes then begin
          if String.equal run "Fail" || String.equal run "Succeed" then under_fail := true
        end
        else if !at_start && not lead_letter then ()  (* [Timeout 5] *)
        else if !at_start then begin
          at_start := false;
          if String.equal run "From" then from_at := Some !i;
          if not !under_fail then begin
            if String.equal run "Module" then cmd_module := true
            else if String.equal run "Section" then frames := ref false :: !frames
            else if String.equal run "End" then begin
              match !frames with
              | f :: rest ->
                frames := rest;
                if !closed && !f then found "End (of a module, or of a section that loads or imports)"
                else if !closed && !restored then found "End (after a Reset or Back)"
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
      end
      end;
      i := !j
    end
    else begin
      (* A sentence ends at a dot followed by a space or the end; a bullet or
         a brace before a command leaves it at the start. *)
      if c = '.' && (!i + 1 >= n || String.contains " \n\t\r" text.[!i + 1])
         && not (!i > 0 && text.[!i - 1] = '.') then begin
        at_start := true; under_fail := false; cmd_module := false; from_at := None
      end;
      step ()
    end
  done;
  !result, !commands

(* The first late command with its line, and the offset of the last one's
   word. *)
let scan_late_events ?imports_late text =
  let first, commands = scan_late_commands ?imports_late text in
  first, (match commands with c :: _ -> Some c.lc_offset | [] -> None)

let scan_late_rebind text = fst (scan_late_events text)

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
     commit binary-equivalence-taiga's Dockerfile pins. Every BET memory
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

let unaudited_plugin () =
  match !toolchain_now with
  | None -> None
  | Some tc ->
    List.find_opt
      (fun (name, _) -> not (!plugin_audit name || List.mem name audited_outside_tree))
      (tc ()).R.plugins

(* The bound that the late commands of a scan (last first) give. *)
let late_bound commands =
  let rec go requires = function
    | { lc_offset; lc_require = Some r } :: rest -> go ((lc_offset, r) :: requires) rest
    | { lc_offset; lc_require = None } :: _ -> { lb_last = Some lc_offset; lb_requires = List.rev requires }
    | [] -> { lb_last = None; lb_requires = List.rev requires }
  in
  go [] commands

type source_rebind =
  | No_late_event
  | Late_events of string * int * late_bound * late_bound
      (** the first command, its line, the bound, and the bound when
          [Import] and [Export] are not late *)
  | Unreadable_source

let source_rebind = function
  | None -> No_late_event
  | Some path ->
    match read_file path with
    | text ->
      (match scan_late_commands text with
       | Some (cmd, line), (_ :: _ as commands) ->
         Late_events (cmd, line, late_bound commands,
                      late_bound (snd (scan_late_commands ~imports_late:false text)))
       | _ -> No_late_event)
    | exception (Sys_error _ | End_of_file) -> Unreadable_source

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

(* Whether the late [Require] at [offset] names only libraries loaded now. *)
let loads_nothing (offset, r) =
  let resolved =
    match Hashtbl.find_opt require_resolutions offset with
    | Some t -> t
    | None ->
      let t = !require_resolver r.rq_from r.rq_names in
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

(* Measurement (BET-84, ReplayFine): each [Require] run while replay is on,
   with its sentence's offset and whether every library it names was
   already loaded before it ran. The summary lists them. *)
let requires_seen : (int * bool) list ref = ref []

(* Where the first proof this file replayed opens. A replay relies on no
   later [Require] loading a library ({!opens_before_late_command}). *)
let first_hit : int option ref = ref None

(* A [Require] after a replayed proof that loads a library all the same
   means the decision read the text or the load path otherwise than the
   [Require] does. The proofs already replayed cannot run their tactics
   now, so the compile stops. *)
let note_require ~already_loaded =
  match !options with
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
    Hashtbl.reset miss_detail;
    requires_seen := [];
    first_hit := None;
    Hashtbl.reset require_resolutions;
    Hashtbl.reset proof_provided;
    pending_counters := [];
    let index = Hashtbl.create 256 in
    let registered_object = ref None in
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
           if refusal = None then begin
             List.iter (fun (p : R.proof) -> Hashtbl.replace index p.R.name p) file.R.proofs;
             (* The registration's object sits beside its record, under the
                same name: a registration tree, and a directory of records
                that a registration published with their objects. *)
             let base =
               if Filename.check_suffix path ".proof-record.jsonl" then
                 Filename.chop_suffix path ".proof-record.jsonl"
               else Filename.remove_extension path
             in
             registered_object := Some (base ^ ".vo", file.R.trailer.R.vo_opaques)
           end;
           refusal)
    in
    (* The registration ran its process-wide cache fences from its start
       ([Proof_recorder.start]); a replay that does not run them would let
       a dirty history here match the clean one recorded there. From here
       on they run at each decision ({!decide}). *)
    let refusal, refused_detail, late, late_no_imports =
      match refusal with
      | Some _ -> refusal, None, no_late, no_late
      | None ->
        match source_rebind source with
        | Unreadable_source -> Some "rebind", Some "an unreadable source", no_late, no_late
        | Late_events (cmd, line, late, late_no_imports) ->
          let bound = function None -> "no proof" | Some b -> Printf.sprintf "proofs before byte %d" b in
          let requires =
            match List.length late_no_imports.lb_requires with
            | 0 -> ""
            | 1 -> "; then 1 Require, late if it loads a library"
            | k -> Printf.sprintf "; then %d Requires, each late if it loads a library" k
          in
          let detail =
            match late.lb_last with
            | Some last when late_no_imports.lb_last <> Some last ->
              Printf.sprintf "%s at line %d; %s run%s (byte %d after an export Register)"
                cmd line (bound late_no_imports.lb_last) requires last
            | _ -> Printf.sprintf "%s at line %d; %s run%s" cmd line (bound late_no_imports.lb_last) requires
          in
          None, Some detail, late, late_no_imports
        | No_late_event -> None, None, no_late, no_late
    in
    if refusal = None then Proof_recorder.start_tracking ();
    toolchain_now := Some toolchain;
    sentence_loc := None;
    open_depth := 0;
    state := Some { f_index = index; f_wall0 = process_start; f_refused = refusal;
                    f_refused_detail = refused_detail; f_late = late;
                    f_late_no_imports = late_no_imports;
                    f_object = !registered_object;
                    f_candidate = None }

let registered_object () = match !state with Some st -> st.f_object | None -> None

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
   late-command rule above (no proof replays before the file's last late
   command) is what keeps later tactics seeing what stock sees. *)
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
   counter that no [register_counter] can move. The declaration makes the
   rest — the levels and constraints, the constraint sources, and the
   schemes, which travel with the term's side effects. A proof that raises a
   warning is ineligible ([CWarnings.warn]), so no warning is to be raised
   again.

   The universe and sort counters are not here: the stored term carries
   them, and the precheck compares them. Every other registered counter is
   moved at the closer by [advance_counters]. *)
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
  (match bound.lb_last with Some last -> here <= last | None -> false)
  || List.exists (fun ((offset, _) as rq) -> here <= offset && not (loads_nothing rq)) bound.lb_requires

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
           Some { c_name = name; c_proof = p; c_offset = sentence_offset (); c_provided = provided ();
                  c_counters = counter_starts () })

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
  | Some ({ f_candidate = Some { c_name = name; c_proof = p; c_offset; c_provided = at_start;
                                 c_counters = starts };
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

