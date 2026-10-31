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

module ReadKey = struct
  type t = { row : string; channel : string; key : string }
  let equal a b = String.equal a.key b.key && String.equal a.channel b.channel && String.equal a.row b.row
  let hash a = Hashtbl.hash (a.row, a.channel, a.key)
end

module ReadTbl = Hashtbl.Make (ReadKey)

type proof_state = {
  mutable p_name : string;
  p_statement : string;
  p_position : R.position;
  p_toolchain_key : R.toolchain_key;
  mutable p_start_tables : R.read list;
  p_reads : R.read Queue.t;
  p_seen : unit ReadTbl.t;  (** the keys already recorded *)
  p_ineligible : R.ineligible Queue.t;
  p_ineligible_seen : (string * string, unit) Hashtbl.t;
  p_sentences : string Queue.t;
  p_levels : string Queue.t;
  p_constraints : string Queue.t;
  p_schemes : string Queue.t;
  p_sources : string Queue.t;
  p_counters : (string, int) Hashtbl.t;
  p_counter_order : string Queue.t;
  p_wall0 : float;
  p_cpu0 : float;
  mutable p_span_start : int option;  (** first byte of the statement's sentence *)
  mutable p_depth : int;  (** 0 for the outermost proof; >0 inside a nested one *)
}

type file_state = {
  f_header : R.header;
  f_toolchain : unit -> R.toolchain;
  f_buf : Buffer.t;
  f_wall0 : float;
  f_cpu0 : float;
  mutable f_count : int;
  mutable f_proof : proof_state option;
  mutable f_suspended : int;  (** >0 inside [without_recording] *)
  mutable f_pending : ((unit -> string) * (int * int) option) option;  (** the sentence being run *)
  mutable f_nested_closed : bool;
      (** a nested proof closed during the sentence being run, and the proof
          around it is still open *)
}

(* The one bit every choke point tests. It is false unless a proof is open
   and recording is not suspended, so a compile without the option pays one
   load and one branch per choke point. *)
let recording = ref false

let state : file_state option ref = ref None

(* Changes at each [open_proof], so that a choke point can empty its own
   memo of already-recorded keys. *)
let gen = ref 0
let generation () = !gen

let active () = !recording

(* Whether this process records or replays at all. [start] sets it, and so
   does the replay's configuration; nothing clears it, as one process
   compiles one file. The toplevel, [Declare] and [Vernacentries] test it
   before they build what a hook takes (a sentence's span and digest
   closure, a proof's path, position and universe snapshot, a closer's
   declaration closure and result pair), so a compile with neither option
   takes the stock path (deep review of 079bc4cb71, DR-2, and of
   26528c8a34, R2-1). *)
let in_use_flag = ref false

let in_use () = !in_use_flag

let set_in_use () = in_use_flag := true

(* Set by a compile that replays and does not record: a process-wide cache
   fence must run there too, or a clean registration history would match a
   dirty replay history. *)
let tracking_only = ref false

let start_tracking () = tracking_only := true

let tracking () =
  !tracking_only || (match !state with Some _ -> true | None -> false)

(* The first fence this process tripped. A process-wide cache that a command
   made stale stays stale for the rest of the process, so the fence is never
   cleared: every proof from here on is ineligible for the same reason. *)
let fence_state : (string * string) option ref = ref None

(* The checks of the process-wide cache fences, registered at module load by
   the module that owns each cache. A check compares what a cache may hold
   with the state it caches, and calls [trip_fence] on a difference. They run
   at each proof's start and end and when a replay asks [fence_tripped], so a
   state that changed behind the cache (a re-registration, a section end that
   restores a table) is seen before the next proof is recorded or replayed. *)
let fence_checks : (unit -> unit) Queue.t = Queue.create ()

let register_fence_check f = Queue.add f fence_checks

let run_fence_checks () = if tracking () then Queue.iter (fun f -> f ()) fence_checks

let fence_tripped () = run_fence_checks (); !fence_state

(* The .vo digest of a loaded library, installed by the toplevel. A constant
   of a required library is recorded by that digest and not by its body: the
   library's digest already pins every constant the library holds, and its
   body can be a megabyte of term. [None] for the library being compiled. *)
let library_digest_hook : (string -> string option) ref = ref (fun _ -> None)

let set_library_digest f = library_digest_hook := f

let library_digest name = !library_digest_hook name

let current_name () =
  match !state with
  | Some { f_proof = Some p; _ } -> Some p.p_name
  | Some { f_proof = None; _ } | None -> None

(* The [Load]s that run now. A loaded file's sentences run inside the one
   sentence that loads it, so the toplevel keeps none of them as a proof's
   sentences (key item 1) and decides no proof among them (INFRA-361 gap 2). *)
let load_depth = ref 0

let in_load () = !load_depth > 0

let loading f =
  incr load_depth;
  match f () with
  | v -> decr load_depth; v
  | exception e ->
    let bt = Printexc.get_raw_backtrace () in
    decr load_depth; Printexc.raise_with_backtrace e bt

let set_recording st =
  recording := st.f_suspended = 0 && st.f_proof <> None

let cpu_time () = let t = Unix.times () in t.Unix.tms_utime +. t.Unix.tms_stime

let peak_rss_kb () = Proof_limits.peak_rss_kb ()

(* BET-84: how a proof's stored term is kept. Off, the blob is the whole
   closed proof, the global universe graph included. [no_graph] leaves the
   graph out (replay rebuilds it); [vo_ref] keeps the proof term as its
   index in the opaque table of the [.vo] this compile writes. *)
let opt_no_graph = ref false
let opt_vo_ref = ref false

let vo_referred = ref false

let set_stored_format ~no_graph ~vo_ref = opt_no_graph := no_graph; opt_vo_ref := vo_ref
let stored_without_graph () = !opt_no_graph
let stored_by_vo_ref () = !opt_vo_ref
let note_vo_ref () = vo_referred := true

let start ~library ~source ~source_digest ~toolchain ~skip_qed_typecheck ~tables_at_start =
  in_use_flag := true;
  vo_referred := false;
  let header = R.{
      version = R.format_version;
      library; source; source_digest;
      toolchain = toolchain ();
      memory_cap = Proof_limits.memory_cap ();
      rlimit_as = Proof_limits.rlimit "Max address space";
      rlimit_data = Proof_limits.rlimit "Max data size";
      overcommit_memory = Proof_limits.overcommit_memory ();
      skip_qed_typecheck;
      tables_at_start;
    }
  in
  let buf = Buffer.create 65536 in
  R.output_header buf header;
  state := Some {
      f_header = header;
      f_toolchain = toolchain;
      f_buf = buf;
      f_wall0 = Unix.gettimeofday ();
      f_cpu0 = cpu_time ();
      f_count = 0;
      f_proof = None;
      f_suspended = 0;
      f_pending = None;
      f_nested_closed = false;
    };
  recording := false

(* The sources of start-of-proof table digests. They register when their
   module loads, before any compile starts, so the registry is global and
   not part of the compile's state. *)
let tables : (unit -> R.read list) Queue.t = Queue.create ()

let register_tables f = Queue.add f tables

(* The same digests as values. The replay side evaluates them at the proof
   it is about to replay, so the recorded value and the value now are made
   the same way. *)
let table_reads () = List.rev (Queue.fold (fun acc f -> List.rev_append (f ()) acc) [] tables)

module Addr = Hashtbl.Make (struct
    type t = Obj.t
    let equal = ( == )
    (* The address, for the reason {!Proof_record} gives for its memo: a
       structural hash reads a bounded prefix, so look-alike values share a
       bucket. A value the GC moved misses and is digested again; its digest
       is the same. *)
    let hash (o : Obj.t) = (Obj.magic o : int) lsr 3
  end)

(* One digest per global-environment value per compile. Emptied with the
   rest of the state, so a compile without the option holds nothing. *)
let digest_cache : string Addr.t = Addr.create 1024

(* The last value of one start read and its digest (see [digest_slot]). Every
   slot is emptied with the rest of the state. *)
type slot = (Obj.t * string) option ref

let slots : slot list ref = ref []

let slot () = let s = ref None in slots := s :: !slots; s

let stop () =
  state := None; recording := false; Addr.reset digest_cache; R.reset_memo ();
  vo_referred := false;
  List.iter (fun s -> s := None) !slots

(* The digest memo and the address cache hold a strong reference to every
   value they digested. A replay-only compile never calls [stop], so it
   empties them after each proof's decision, which bounds them by one
   proof's reads (review P3Deep F7). *)
let reset_caches () = Addr.reset digest_cache; R.reset_memo ()

let write ?(vo_opaques = fun () -> None) path =
  match !state with
  | None -> ()
  | Some st ->
    R.output_trailer st.f_buf R.{
        file_wall_s = Unix.gettimeofday () -. st.f_wall0;
        file_cpu_s = cpu_time () -. st.f_cpu0;
        peak_rss_kb = peak_rss_kb ();
        proof_count = st.f_count;
        vo_opaques = (if !vo_referred then vo_opaques () else None);
      };
    let oc = open_out_bin path in
    Buffer.output_buffer oc st.f_buf;
    close_out oc;
    stop ()

let add_ineligible p ~reason ~detail =
  let key = (reason, detail) in
  if not (Hashtbl.mem p.p_ineligible_seen key) then begin
    Hashtbl.add p.p_ineligible_seen key ();
    Queue.add R.{ reason; detail } p.p_ineligible
  end

let open_proof ~name ~statement ~position =
  match !state with
  | None -> ()
  | Some st ->
    match st.f_proof with
    | Some p ->
      (* A sub-proof of the open one: abstract, a nested obligation. Its
         reads stay with the open proof, which cannot be replayed. *)
      p.p_depth <- p.p_depth + 1;
      let key = ("nested_proof", name) in
      if not (Hashtbl.mem p.p_ineligible_seen key) then begin
        Hashtbl.add p.p_ineligible_seen key ();
        Queue.add R.{ reason = "nested_proof"; detail = name } p.p_ineligible
      end
    | None ->
      let span_start = match st.f_pending with Some (_, Some (bp, _)) -> Some bp | _ -> None in
      (* The proof is opened first, so that a table this cannot digest marks
         this proof ineligible and not the one before it. *)
      incr gen;
      st.f_proof <- Some {
          p_name = name;
          p_statement = statement ();
          p_position = position;
          p_toolchain_key = R.toolchain_key (st.f_toolchain ());
          p_start_tables = [];
          p_reads = Queue.create ();
          p_seen = ReadTbl.create 256;
          p_ineligible = Queue.create ();
          p_ineligible_seen = Hashtbl.create 16;
          p_sentences = Queue.create ();
          p_levels = Queue.create ();
          p_constraints = Queue.create ();
          p_schemes = Queue.create ();
          p_sources = Queue.create ();
          p_counters = Hashtbl.create 8;
          p_counter_order = Queue.create ();
          p_wall0 = Unix.gettimeofday ();
          p_cpu0 = cpu_time ();
          p_span_start = span_start;
          p_depth = 0;
        };
      set_recording st;
      (match st.f_proof with
       | None -> ()
       | Some p ->
         p.p_start_tables <- (Queue.fold (fun acc f -> List.rev_append (f ()) acc) [] tables |> List.rev);
         run_fence_checks ();
         (match !fence_state with
          | None -> ()
          | Some (reason, detail) -> add_ineligible p ~reason ~detail))

(* The sentence being run belongs to the proof that is open when it ends,
   so the statement's own sentence is the first of its proof's. *)
let take_pending st p =
  match st.f_pending with
  | None -> ()
  | Some (d, _) -> st.f_pending <- None; Queue.add (d ()) p.p_sentences

let pending_span st = match st.f_pending with Some (_, span) -> span | None -> None

let sentence ?span digest run =
  match !state with
  | None -> run ()
  | Some st ->
    let outer = st.f_pending in
    st.f_pending <- Some (digest, span);
    st.f_nested_closed <- false;
    let finish () =
      (match st.f_proof with Some p when p.p_depth = 0 -> take_pending st p | Some _ | None -> ());
      st.f_pending <- outer
    in
    (match run () with
     | v -> finish (); v
     | exception e -> let bt = Printexc.get_raw_backtrace () in
       finish (); Printexc.raise_with_backtrace e bt)

let nested_closed () =
  match !state with
  | Some { f_nested_closed; _ } -> f_nested_closed
  | None -> false

let close_proof ~closer ~kernel_check ~replay =
  match !state with
  | None -> ()
  | Some st ->
    match st.f_proof with
    | None -> ()
    | Some p when p.p_depth > 0 -> p.p_depth <- p.p_depth - 1; st.f_nested_closed <- true
    | Some p ->
      let span = match p.p_span_start, pending_span st with
        | Some bp, Some (_, ep) when ep > bp -> Some (bp, ep)
        | _ -> None
      in
      take_pending st p;
      (* A fence can trip while the proof runs (a plugin closure installed by
         a tactic, a lazy rebound by its declaration), and the next check
         would only come at the next proof's start: check here too, so the
         proof that was open when it tripped is not written eligible. *)
      run_fence_checks ();
      (match !fence_state with
       | None -> ()
       | Some (reason, detail) -> add_ineligible p ~reason ~detail);
      let list q = List.of_seq (Queue.to_seq q) in
      let proof = R.{
          name = p.p_name;
          statement = p.p_statement;
          sentences = R.digest_value (list p.p_sentences);
          closer;
          toolchain_key = p.p_toolchain_key;
          position = p.p_position;
          ineligible = list p.p_ineligible;
          reads = list p.p_reads;
          start_tables = p.p_start_tables;
          writes = {
            universe_levels = list p.p_levels;
            counters = List.map (fun n -> (n, Hashtbl.find p.p_counters n)) (list p.p_counter_order);
            constraints = list p.p_constraints;
            schemes = list p.p_schemes;
            constraint_sources = list p.p_sources;
          };
          kernel_check;
          wall_s = Unix.gettimeofday () -. p.p_wall0;
          cpu_s = cpu_time () -. p.p_cpu0;
          span;
          (* An ineligible proof stores no term (BET-84 spec, gate step 2:
             "each ineligible class: the registration stores no term").
             The ineligibility is final only here: a reason can be added
             after the closer computed the term, by the declaration. *)
          replay = (if Queue.is_empty p.p_ineligible then replay else None);
        }
      in
      R.output_proof st.f_buf proof;
      st.f_count <- st.f_count + 1;
      st.f_proof <- None;
      set_recording st

(* An [Abort] drops the proof and writes no entry. Without this the recorder
   would keep the aborted proof open and swallow every proof after it. *)
let drop_proof () =
  match !state with
  | None -> ()
  | Some st ->
    match st.f_proof with
    | None -> ()
    | Some p when p.p_depth > 0 -> p.p_depth <- p.p_depth - 1
    | Some _ -> st.f_pending <- None; st.f_proof <- None; set_recording st

(* [Abort All] drops every open proof, nested ones included. *)
let drop_all_proofs () =
  match !state with
  | None -> ()
  | Some st -> st.f_pending <- None; st.f_proof <- None; set_recording st

let set_name name =
  match !state with
  | None | Some { f_proof = None; _ } -> ()
  | Some { f_proof = Some p; _ } -> if p.p_depth = 0 then p.p_name <- name

(* Writes are collected whenever a proof is open, [without_recording]
   included: a write the declaration makes at the closer is the proof's. *)
let with_proof f =
  match !state with
  | None | Some { f_proof = None; _ } -> ()
  | Some { f_proof = Some p; _ } -> f p

let writing () =
  match !state with
  | Some { f_proof = Some _; _ } -> true
  | Some { f_proof = None; _ } | None -> false

let write_universes ~levels ~constraints =
  with_proof (fun p ->
      List.iter (fun l -> Queue.add l p.p_levels) levels;
      List.iter (fun c -> Queue.add c p.p_constraints) constraints)

let write_scheme s = with_proof (fun p -> Queue.add s p.p_schemes)

let created_in p name =
  (not (Queue.is_empty p.p_schemes))
  && (let n = name () in Queue.fold (fun found s -> found || String.equal s n) false p.p_schemes)

let write_constraint_source s = with_proof (fun p -> Queue.add s p.p_sources)

let write_counters l =
  with_proof (fun p ->
      List.iter
        (fun (name, n) ->
           if n <> 0 then
             match Hashtbl.find_opt p.p_counters name with
             | None -> Hashtbl.add p.p_counters name n; Queue.add name p.p_counter_order
             | Some m -> Hashtbl.replace p.p_counters name (m + n))
        l)

let read ~row ~channel ~key ~value =
  if !recording then
    match !state with
    | None | Some { f_proof = None; _ } -> ()
    | Some { f_proof = Some p; _ } ->
      let key = key () in
      let k = ReadKey.{ row; channel; key } in
      (* Only the first value of a key is kept, and a repeat does not compute
         the value again: the global state a tactic reads moves inside a
         proof only through the proof's own writes (a scheme it creates) or
         through a command or sub-proof that already makes it ineligible, so
         the first value is the one replay sees. A read keyed by a constant
         the proof created itself is not kept at all: it is not an input of
         the proof, replay declares the constant again with the stored term,
         and the state at the proof's start, where replay reads, does not
         hold it (fixture write_scheme_rewrite). *)
      if not (ReadTbl.mem p.p_seen k) && not (created_in p (fun () -> key)) then begin
        let v = value () in
        ReadTbl.add p.p_seen k ();
        Queue.add R.{ row; channel; key; value = v } p.p_reads
      end

(* The same, for hot choke points whose printed key is costly: a repeat is
   found by the raw name [id], compared structurally, and [key] and [value]
   are called only for a new one. *)
module IdKey = struct
  type t = { irow : string; ichannel : string; id : Obj.t }
  let equal a b = a.id = b.id && String.equal a.ichannel b.ichannel && String.equal a.irow b.irow
  let hash a = Hashtbl.hash (a.irow, a.ichannel, a.id)
end

module IdTbl = Hashtbl.Make (IdKey)

let seen_ids : unit IdTbl.t = IdTbl.create 1024
let seen_ids_gen = ref (-1)

let read_by ~row ~channel ~id ~key ~value =
  if !recording then begin
    if !seen_ids_gen <> !gen then (IdTbl.reset seen_ids; seen_ids_gen := !gen);
    let k = IdKey.{ irow = row; ichannel = channel; id = Obj.repr id } in
    if not (IdTbl.mem seen_ids k) then begin
      IdTbl.add seen_ids k ();
      read ~row ~channel ~key ~value
    end
  end

let ineligible ~reason ~detail =
  match !state with
  | None | Some { f_proof = None; _ } -> ()
  | Some { f_proof = Some p; _ } -> add_ineligible p ~reason ~detail

let trip_fence ~reason ~detail =
  (match !fence_state with None -> fence_state := Some (reason, detail) | Some _ -> ());
  ineligible ~reason ~detail

(* A setter of a process-wide closure, such as the unifier behind
   Evarconv.set_evar_conv: Rocq's own modules call it [stock] times when
   they load, before any plugin can. A later call installs a plugin's
   closure, which can read plugin state no read sees (unicoq's Set Use
   Unicoq installs its unifier, and Unset does not remove it), so from then
   on the fence is tripped (Claude review of the fix round at 467292ce69,
   findings 1 and 2). *)
let closure_setter ~what ~stock =
  let sets = ref 0 in
  register_fence_check (fun () ->
      if !sets > stock then trip_fence ~reason:"plugin_hook" ~detail:what);
  fun () -> incr sets

let digest ?locs ~what v =
  match R.digest_value ?locs v with
  | d -> d
  | exception R.Unhashable msg ->
    ineligible ~reason:"unhashable" ~detail:(what ^ ": " ^ msg);
    "unhashable"

let digest_cached ~what v =
  let o = Obj.repr v in
  match Addr.find_opt digest_cache o with
  | Some d -> if d = "unhashable" then ineligible ~reason:"unhashable" ~detail:what; d
  | None ->
    let d = digest ~what v in
    Addr.add digest_cache o d;
    d

(* The file this compile reads, so that a digest can leave out the
   locations of that file: a value that differs only by where in the file it
   was written (a hint written two lines lower) digests the same. *)
let locs_source : Loc.source option ref = ref None

let set_locs_source src = locs_source := Some src

let compiled_source () = !locs_source

let digest_cached_by ~what ~key view =
  let o = Obj.repr key in
  match Addr.find_opt digest_cache o with
  | Some d -> if d = "unhashable" then ineligible ~reason:"unhashable" ~detail:what; d
  | None ->
    let d = digest ?locs:!locs_source ~what (view ()) in
    Addr.add digest_cache o d;
    d

(* A cached "unhashable" is a stand-in shared by every value that cannot be
   digested, so each proof that reuses it is marked, not only the first one
   (Claude gate at 0f8d815732, finding 6). *)
let digest_slot s ~what v =
  let o = Obj.repr v in
  match !s with
  | Some (o0, d) when o0 == o ->
    if d = "unhashable" then ineligible ~reason:"unhashable" ~detail:what;
    d
  | Some _ | None ->
    let d = digest ~what v in
    s := Some (o, d);
    d

let without_recording f =
  match !state with
  | None -> f ()
  | Some st ->
    st.f_suspended <- st.f_suspended + 1;
    recording := false;
    let finish () = st.f_suspended <- st.f_suspended - 1; set_recording st in
    (match f () with
     | v -> finish (); v
     | exception e -> let bt = Printexc.get_raw_backtrace () in
       finish (); Printexc.raise_with_backtrace e bt)
