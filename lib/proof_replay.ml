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
  mutable outcomes : (string * string * string option) list;  (** newest first *)
}

type file_state = {
  f_index : (string, R.proof) Hashtbl.t;
  f_wall0 : float;
  f_refused : string option;
  mutable f_candidate : candidate option;
}

let options : options option ref = ref None
let state : file_state option ref = ref None

let counts = {
  n_proofs = 0; n_hits = 0; m_key = 0; m_read = 0; m_ineligible = 0; m_missing = 0;
  charged = 0.; registered = 0.; outcomes = [];
}

let channel_miss : (string, int) Hashtbl.t = Hashtbl.create 16

let configure ~source ~ratio ~budget ~peak_limit_kb =
  options := Some { o_source = source; o_ratio = ratio; o_budget = budget; o_peak_limit_kb = peak_limit_kb }

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
      @ (match !record_of_vo with Some p when not (Filename.is_relative p) -> [] | Some p -> [ p ] | None -> [])
    in
    List.find_opt Sys.file_exists (List.map (Filename.concat dir) places)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(* A compile that ran under a limit which can end an allocation before the
   cgroup kill is not replayed, in either direction: under such a limit a
   proof can fail where the other run's did not, and a stored term would
   hide it (BET-84 spec, "When a stored term is used"). *)
let limits_refusal (h : R.header) =
  if h.R.rlimit_as <> "unlimited" || h.R.rlimit_data <> "unlimited" then Some "rlimit"
  else if h.R.overcommit_memory = "2" then Some "overcommit"
  else None

let own_limits_refusal () =
  if Proof_limits.rlimit "Max address space" <> "unlimited"
     || Proof_limits.rlimit "Max data size" <> "unlimited"
  then Some "rlimit"
  else if Proof_limits.overcommit_memory () = "2" then Some "overcommit"
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

let start ~library ~toolchain =
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
    Hashtbl.reset channel_miss;
    Hashtbl.reset proof_provided;
    pending_counters := [];
    let index = Hashtbl.create 256 in
    let refusal =
      match record_path ~library opts.o_source with
      | None -> Some "bad_record"
      | Some path ->
        (match R.parse_string (read_file path) with
         | exception _ -> Some "bad_record"
         | file ->
           let refusal =
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
    state := Some { f_index = index; f_wall0 = process_start; f_refused = refusal; f_candidate = None }

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

let miss_read name channel =
  counts.m_read <- counts.m_read + 1;
  outcome name "read" (Some channel);
  Hashtbl.replace channel_miss channel (1 + Option.default 0 (Hashtbl.find_opt channel_miss channel))

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

   The providers answer first: they give, as one list, the channels that
   have no single read point, from the same function the recorder takes
   them from. A read of such a channel that the providers do not list is a
   miss: a provider that stopped answering must not look like a value that
   stayed the same. Every other channel has its evaluator, and a channel
   with none, or an evaluator that cannot answer, is a miss too. *)
let first_read_mismatch (p : R.proof) ~at_start =
  let now (r : R.read) =
    let table, channels = at_start in
    match Hashtbl.find_opt proof_provided (r.R.channel, r.R.key) with
    | Some v -> Value v
    | None ->
    if Hashtbl.mem channels r.R.channel then
      match Hashtbl.find_opt table (r.R.channel, r.R.key) with
      | Some v -> Value v
      | None -> Unknown
    else
      match Hashtbl.find_opt evaluators r.R.channel with
      | None -> Unknown
      | Some f -> (match f r.R.key with v -> v | exception _ -> Unknown)
  in
  let rec loop = function
    | [] -> None
    | (r : R.read) :: rest ->
      (match now r with
       | Unknown -> Some r.R.channel
       | Value v -> if v = r.R.value then loop rest else Some r.R.channel)
  in
  loop (p.R.start_tables @ p.R.reads)

let decide ~sentences ~closer =
  match !state with
  | None | Some { f_candidate = None; _ } | Some { f_refused = Some _; _ } -> None
  | Some ({ f_candidate = Some { c_name = name; c_proof = p; c_provided = at_start; c_counters = starts };
            _ } as st) ->
    st.f_candidate <- None;
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
          | Some channel -> miss_read name channel; None
          | None ->
            counts.n_hits <- counts.n_hits + 1;
            outcome name "hit" None;
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
            | Some c ->
              Printf.sprintf "{\"name\":%s,\"outcome\":%s,\"channel\":%s}" (quote name) (quote kind) (quote c))
         counts.outcomes)
  in
  Printf.sprintf
    "{\"version\":1,\"proofs\":%d,\"hits\":%d,\
     \"misses\":{\"key\":%d,\"read\":%d,\"ineligible\":%d,\"missing_record\":%d},\
     \"refused\":%s,\"charged_s\":%.6f,\"registered_s\":%.6f,\"elapsed_s\":%.6f,\"killed\":%s,\
     \"channel_misses\":[%s],\"outcomes\":[%s]}\n"
    counts.n_proofs counts.n_hits counts.m_key counts.m_read counts.m_ineligible counts.m_missing
    (match refused () with None -> "null" | Some r -> quote r)
    counts.charged counts.registered elapsed
    (if killed then "true" else "false")
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
