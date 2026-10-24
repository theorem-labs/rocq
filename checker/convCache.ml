(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The unit cache of the native conversion.

    With [-j N] for [N > 1], a worker whose cast runs past the VM budget
    compiles the definitions its conversion needs into a unit of its own
    and publishes it, so that the other workers load that code instead of
    compiling it again. Each worker is both producer and consumer; the
    main process only makes the directory and removes it.

    A unit of the cache holds definitions only, never a conversion, so
    loading it runs nothing of the producer's check, and it carries its
    own symbols, so the process that loads it needs nothing of the process
    that wrote it.

    {6 What may be reused}

    A definition's code calls the code of the globals its body names,
    through the names those globals had in the producer. So the same
    declaration is not enough: one check binds one name to two bodies (a
    module's type and its implementation, [Mod_checking]), and the code of
    a definition that calls the implementation must not be used where the
    name is abstract.

    Each definition therefore carries a key: its own declaration and the
    names of the globals its code names, marshalled. A consumer recomputes
    the key of every definition of a unit, and of the units it refers to,
    from its own environment, and reuses the unit only when every key is
    equal byte for byte. Producer and consumer are forks of one process
    and marshal the declaration objects they inherited, so equal
    declarations give equal bytes; a difference only costs a reuse. The
    digest of a key is an index, never the decision.

    {6 Claims}

    Right after its closure walk, before it generates code, a worker
    claims each definition of its closure that no live claim and no
    publication holds: one file per key, created with [O_EXCL], holding
    the producer's pid. Its unit refers only to units already published,
    so compiling its own claim never waits, and it publishes what it owns
    before it waits on anyone: the wait-for relation has no cycle. Every
    path out of the worker after a claim, the fallback to the VM included,
    releases the claim. A waiter stops when the claim resolves, when the
    claimant's pid has gone, or at a backstop timeout, and then compiles
    those definitions itself. *)

open Names
open Nativecode

let debug = CDebug.create ~name:"conv-cache" ()

(** {6 What a unit publishes} *)

type entry = {
  e_def : definition;
  e_key : string;                      (* the marshalled key, see above *)
  e_prefix : string;      (* the prefix of the part that defines it *)
}

type manifest = {
  m_prefix : string;                       (* the unit's module prefix *)
  m_parts : string list;  (* the prefixes of its parts; [] for one module *)
  m_cmxs : string;                              (* the file's basename *)
  m_digest : string;                     (* [Digest.file] of that file *)
  m_units : string list;    (* prefixes of the units it refers to, in order *)
  m_defs : entry list;                 (* every definition it defines *)
}

let enabled = ref false
let main_pid = ref 0
let cache_dir = ref ""

(* Counters and timings of the cast being run, for the measurement. *)
let c_status = ref "-"
let c_reused = ref 0
let c_units = ref 0
let c_copied = ref 0
let c_copied_bytes = ref 0
let c_manifest_bytes = ref 0

let reset_counters () =
  c_status := "-"; c_reused := 0; c_units := 0; c_copied := 0;
  c_copied_bytes := 0; c_manifest_bytes := 0

(** {6 Files} *)

let ( / ) = Filename.concat

let write_atomically path content =
  let tmp = Printf.sprintf "%s.tmp%d" path (Unix.getpid ()) in
  let fd = Unix.openfile tmp Unix.[O_WRONLY; O_CREAT; O_TRUNC; O_CLOEXEC] 0o600 in
  let () =
    Fun.protect ~finally:(fun () -> Unix.close fd) @@ fun () ->
    let len = String.length content in
    let rec go off =
      if off < len then go (off + Unix.write_substring fd content off (len - off))
    in
    go 0
  in
  Unix.rename tmp path

let read_file path =
  match open_in_bin path with
  | exception Sys_error _ -> None
  | ch ->
    Fun.protect ~finally:(fun () -> close_in ch) @@ fun () ->
    Some (really_input_string ch (in_channel_length ch))

(* The claim files of a key share this base name; see [try_claim]. *)
let claim_file key = !cache_dir / ("k" ^ Digest.to_hex (Digest.string key))

(** {6 The index a worker keeps of what is published and claimed}

    Everything that stands for a definition here is the definition
    itself, never its printed name: a kernel identifier read from an
    object may hold any bytes, '.' included, so two different kernel
    names can print the same, and a cache that keyed on the printed name
    would give one definition's code to another. *)

module DefMap = Map.Make (struct
    type t = definition
    let compare = definition_compare
  end)

let units : (string, manifest) Hashtbl.t = Hashtbl.create 97
(* Every prefix a unit registers, its own and its parts', to the unit's. *)
let part_unit : (string, string) Hashtbl.t = Hashtbl.create 97
let by_def : (string * entry) list DefMap.t ref = ref DefMap.empty
let claims : (string, int) Hashtbl.t = Hashtbl.create 97   (* claim file -> pid *)
let indexed : (string, unit) Hashtbl.t = Hashtbl.create 997       (* files read *)

(* The units this process has loaded from the cache, newest first: a
   unit is loaded only after the units it refers to, so this is a load
   order for any subset of it. *)
let loaded_order : string list ref = ref []

let add_manifest m =
  Hashtbl.replace units m.m_prefix m;
  List.iter (fun p -> Hashtbl.replace part_unit p m.m_prefix) (m.m_prefix :: m.m_parts);
  List.iter (fun e ->
      let others = try DefMap.find e.e_def !by_def with Not_found -> [] in
      by_def := DefMap.add e.e_def ((m.m_prefix, e) :: others) !by_def)
    m.m_defs

let read_manifest file =
  match read_file (!cache_dir / file) with
  | None -> ()
  | Some s ->
    match (Marshal.from_string s 0 : manifest) with
    | m -> add_manifest m
    | exception _ -> ()

(* Read what appeared since the last pass. A file is read once; a claim
   file that has gone is dropped. *)
let refresh_index () =
  let t0 = Unix.gettimeofday () in
  let files = try Sys.readdir !cache_dir with Sys_error _ -> [||] in
  let present = Hashtbl.create 97 in
  Array.iter (fun f ->
      if Filename.check_suffix f ".manifest" then begin
        if not (Hashtbl.mem indexed f) then begin
          Hashtbl.replace indexed f ();
          read_manifest f
        end
      end else if Filename.check_suffix f ".claim" then begin
        let path = !cache_dir / f in
        Hashtbl.replace present path ();
        if not (Hashtbl.mem claims path) then
          match read_file path with
          | Some s -> (try Hashtbl.replace claims path (int_of_string (String.trim s)) with _ -> ())
          | None -> ()
      end)
    files;
  Hashtbl.iter (fun path _ -> if not (Hashtbl.mem present path) then Hashtbl.remove claims path)
    (Hashtbl.copy claims);
  (* r3-b instrumentation *)
  ConvLog.time_add ConvLog.Index (Unix.gettimeofday () -. t0)

(** {6 Keys} *)

module DefHash = Hashtbl.Make (struct
    type t = definition
    let equal = definition_equal
    let hash d = Hashtbl.hash (definition_name d)
  end)

let key_memo : string option DefHash.t = DefHash.create 997

(* The key of a definition, computed from this process's environment. It
   holds what decides whether code compiled elsewhere computes here what
   this declaration computes:
   - the user name, which finds the definition ([definition_name]);
   - the canonical name that its code keeps, if any, as this
     environment has it ([retained_canonical_name]): the code of an axiom,
     an opaque proof, a primitive, a symbol or an inductive holds it in
     its accumulators, which the conversion compares by canonical name;
   - the declaration, and the names of the globals its code calls.
   The canonical name is read from this environment's entry for the user
   name, never from the [Constant.t] at hand: in [verify] that is the
   producer's, from its manifest. *)
let marshal_key env sigma d =
  let refs = List.map definition_name (direct_references env sigma d) in
  let canonical = retained_canonical_name env d in
  match d with
  | Dconst c ->
    let cb = Environ.lookup_constant c env in
    let body = match cb.Declarations.const_body with
      | Declarations.Def t -> `Def t
      | Declarations.OpaqueDef _ -> `Opaque
      | Declarations.Undef _ -> `Undef
      | Declarations.Primitive op -> `Primitive op
      | Declarations.Symbol b -> `Symbol b
    in
    let alias = match cb.Declarations.const_body_code with
      | Some (Vmemitcodes.BCalias kn) -> Some (constant_name kn)
      | Some (Vmemitcodes.BCdefined _) | Some Vmemitcodes.BCconstant | None -> None
    in
    Marshal.to_string
      (`Constant (definition_name d, canonical, body, cb.Declarations.const_hyps,
                  cb.Declarations.const_univ_hyps, cb.Declarations.const_universes, alias, refs))
      []
  | Dind m ->
    (* The whole declaration: a later step may read more of it than the
       relocation tables the code generation reads today. *)
    Marshal.to_string (`Inductive (definition_name d, canonical, Environ.lookup_mind m env, refs)) []

(* [None] when the declaration is not in this environment, or does not
   marshal: such a definition is neither reused nor claimed. A unit of a
   worker forked later can name a constant this process never had, and
   [Environ.lookup_constant] raises an anomaly for it, so every failure
   here is caught, [Sys.Break] apart. *)
let key env sigma d =
  match DefHash.find_opt key_memo d with
  | Some k -> k
  | None ->
    let known = match d with
      | Dconst c -> Environ.mem_constant c env
      | Dind m -> Environ.mem_mind m env
    in
    let k =
      if not known then None
      else match marshal_key env sigma d with
        | s -> Some s
        | exception Sys.Break -> raise Sys.Break
        | exception _ -> None
    in
    DefHash.replace key_memo d k;
    k

(** {6 Reusing} *)

let verified : (string, bool) Hashtbl.t = Hashtbl.create 97

(* A unit may be reused when every definition it defines, and every
   definition of the units it refers to, has in this environment the key
   it had in the producer: the same declaration, the same references, and
   the same canonical name where its code keeps one ([marshal_key]). That
   is more than the call graph of what is reused, and so never reuses
   code the call-graph rule would refuse. *)
let rec verify env sigma prefix =
  match Hashtbl.find_opt verified prefix with
  | Some b -> b
  | None ->
    (* A unit under verification counts as verified: the recursion is on
       the reference graph, which a cycle would make unloadable anyway. *)
    Hashtbl.replace verified prefix true;
    let b = match Hashtbl.find_opt units prefix with
      | None -> false
      | Some m ->
        List.for_all (fun e -> match key env sigma e.e_def with
            | Some k -> String.equal k e.e_key
            | None -> false)
          m.m_defs
        && List.for_all (fun p -> verify env sigma p) m.m_units
    in
    Hashtbl.replace verified prefix b;
    b

let unit_file m = !cache_dir / m.m_cmxs

let digest_ok m =
  match Digest.file (unit_file m) with
  | d -> String.equal (Digest.to_hex d) m.m_digest
  | exception Sys_error _ -> false

(* Load a unit and the units it refers to, in order, each checked against
   the digest its producer published, skipping what this process has
   loaded. Marks every definition of a loaded unit linked to the part
   that defines it: they are all verified. *)
let rec load env sigma prefix =
  if is_loaded_native_file prefix then true
  else match Hashtbl.find_opt units prefix with
    | None -> false
    | Some m ->
      List.for_all (fun p -> load env sigma p) m.m_units
      && digest_ok m
      && (match Nativelib.load_unit ~prefixes:(m.m_prefix :: m.m_parts) (unit_file m) with
          | () ->
            List.iter (fun e -> link_definitions env e.e_prefix [e.e_def]) m.m_defs;
            loaded_order := m.m_prefix :: !loaded_order;
            incr c_units;
            true
          | exception (Dynlink.Error _ | Sys_error _ | Unix.Unix_error _ | CErrors.UserError _ as e) ->
            debug (fun () -> Pp.(str "cache: " ++ str prefix ++ str " failed to load: " ++
                                 str (Printexc.to_string e)));
            Hashtbl.replace verified prefix false;
            false)

(* The published unit a prefix belongs to: its own or one of its parts'. *)
let unit_of_prefix p = Hashtbl.find_opt part_unit p

(* A definition is available to this worker when it is linked to a unit
   of the cache that is published. One linked otherwise (by a conversion
   unit of the main process, inherited at the fork, or by an unpublished
   unit of this worker) cannot be named by a published unit, so the cache
   counts it as not compiled: it is reused, claimed and emitted again. *)
let available env d = match definition_prefix env d with
  | Some p -> Option.has_some (unit_of_prefix p)
  | None -> false

(* Load what the closure can take from the published units. *)
let reuse env sigma closure =
  List.iter (fun d ->
      if not (available env d) then
        match DefMap.find_opt d !by_def with
        | None -> ()
        | Some candidates ->
          let ok (prefix, e) =
            match key env sigma d with
            | Some k when String.equal k e.e_key ->
              verify env sigma prefix && load env sigma prefix
            | Some _ | None -> false
          in
          if List.exists ok candidates then incr c_reused)
    closure

(** {6 Claiming} *)

let held : string list ref = ref []            (* claim files this process owns *)

let release () =
  List.iter (fun f -> try Sys.remove f with Sys_error _ -> ()) !held;
  held := []

let alive pid = match Unix.kill pid 0 with
  | () -> true
  | exception Unix.Unix_error (Unix.ESRCH, _, _) -> false
  | exception Unix.Unix_error _ -> true

(* A claim on a key is a file [<key digest>.<generation>.claim] holding the
   claimant's pid. The live generation is the highest one present. When
   its claimant has exited without resolving it (a worker killed), the
   next worker takes the key over by creating the next generation with
   [O_EXCL]: two workers racing for it cannot both win, and nobody ever
   removes a file another process created. *)
let pid_of file =
  match read_file file with
  | Some s -> (try Some (int_of_string (String.trim s)) with _ -> None)
  | None -> None

let generation_file base g = Printf.sprintf "%s.%d.claim" base g

let rec live_generation base g =
  if Sys.file_exists (generation_file base (g + 1)) then live_generation base (g + 1) else g

let try_claim base =
  let g =
    if not (Sys.file_exists (generation_file base 0)) then 0
    else
      let g = live_generation base 0 in
      let f = generation_file base g in
      match pid_of f with
      | Some pid when alive pid ->
        (* Another worker holds it: remember who, for the wait. *)
        Hashtbl.replace claims f pid;
        -1
      | Some _ | None -> g + 1           (* its claimant is gone: take over *)
  in
  if g < 0 then false
  else
    let file = generation_file base g in
    match Unix.openfile file Unix.[O_WRONLY; O_CREAT; O_EXCL; O_CLOEXEC] 0o600 with
    | fd ->
      let s = string_of_int (Unix.getpid ()) in
      (try ignore (Unix.write_substring fd s 0 (String.length s) : int) with Unix.Unix_error _ -> ());
      Unix.close fd;
      held := file :: !held;
      true
    | exception Unix.Unix_error (Unix.EEXIST, _, _) ->
      (* Another worker won this generation. *)
      (match pid_of file with Some pid -> Hashtbl.replace claims file pid | None -> ());
      false
    | exception Unix.Unix_error _ -> false

(* A worker waits for another's claims only when they are no larger than
   twice what it would compile itself, counted by the size of the
   declarations. A backstop stops every wait: this is measurement code in
   a checker, and a wait that never ends would be a verdict. *)
let wait_limit = 120.

let wait_for files =
  let t0 = Unix.gettimeofday () in
  let rec go () =
    let left = List.filter Sys.file_exists files in
    if CList.is_empty left then ()
    else if Unix.gettimeofday () -. t0 > wait_limit then
      (* r3-b instrumentation: a wait that ends at the backstop (B-54) *)
      ConvLog.event "backstop" [Printf.sprintf "%.3f" (Unix.gettimeofday () -. t0);
                                string_of_int (List.length left)]
    else if not (List.exists (fun f ->
        match read_file f with
        | Some s -> (try alive (int_of_string (String.trim s)) with _ -> false)
        | None -> false) left)
    then ()
    else begin
      (try Unix.sleepf 0.02 with Unix.Unix_error _ -> ());
      go ()
    end
  in
  go ();
  let waited = Unix.gettimeofday () -. t0 in
  (* r3-b instrumentation *)
  ConvLog.time_add ConvLog.Wait waited;
  waited

(** {6 Publishing} *)

(* The prefixes of a unit's parts, other than its root: by name, not by
   their number. A unit cut into one actual part is the module
   [<base>_p1], not [<base>], and that part's prefix must be recorded
   and registered like any other. *)
let part_prefixes prefix parts =
  List.filter (fun p -> not (String.equal p prefix))
    (List.map (fun p -> p.Nativelib.part_prefix) parts)

let publish env prefix cmxs ~digest ~parts defs refs =
  let m = {
    m_prefix = prefix;
    m_parts = part_prefixes prefix parts;
    m_cmxs = Filename.basename cmxs;
    m_digest = digest;
    m_units = refs;
    m_defs = List.map (fun (d, k, p) -> { e_def = d; e_key = k; e_prefix = p }) defs;
  } in
  let s = Marshal.to_string m [] in
  c_manifest_bytes := !c_manifest_bytes + String.length s;
  write_atomically (!cache_dir / (Filename.remove_extension m.m_cmxs ^ ".manifest")) s;
  add_manifest m;
  Hashtbl.replace verified prefix true;
  ignore env

(** {6 What a worker does before it generates a conversion} *)

let prepare env t1 t2 =
  if not !enabled || Unix.getpid () = !main_pid then ()
  else begin
    reset_counters ();
    let sigma = Genlambda.empty_evars env in
    refresh_index ();
    let graph = closure_graph env sigma [t1; t2] in
    let closure = List.map fst graph in
    reuse env sigma closure;
    (* What is left for this cast to compile after the reuse. *)
    let size d = match key env sigma d with None -> 0 | Some k -> String.length k in
    let left () = List.filter (fun d -> not (available env d)) closure in
    let me = Unix.getpid () in
    (* Claim what no live claim and no publication holds. The claim comes
       before any code is generated, so a cast that starts while another
       worker generates the same code already sees the claim. *)
    let claim defs =
      List.filter (fun d -> match key env sigma d with
          | None -> false
          | Some k -> try_claim (claim_file k))
        defs
    in
    (* The claims of the others on what is left, by claimant, and the
       files to wait for. A worker waits only while it holds no claim of
       its own, so no two workers can wait for each other; and only when
       what the others hold is no more than twice what it would compile
       itself, counted by the size of the declarations. *)
    let others defs =
      let sizes = Hashtbl.create 17 and files = Hashtbl.create 17 in
      List.iter (fun d -> match key env sigma d with
          | None -> ()
          | Some k ->
            let base = claim_file k in
            let f = generation_file base (live_generation base 0) in
            match (if Sys.file_exists f then pid_of f else None) with
            | Some pid when pid <> me ->
              Hashtbl.replace sizes pid (size d + (try Hashtbl.find sizes pid with Not_found -> 0));
              Hashtbl.replace files pid (f :: (try Hashtbl.find files pid with Not_found -> []))
            | Some _ | None -> ())
        defs;
      sizes, files
    in
    let mine = ref (claim (left ())) in
    let waited =
      let rest = List.filter (fun d -> not (List.exists (definition_equal d) !mine)) (left ()) in
      let sizes, files = others rest in
      let mine_size = List.fold_left (fun a d -> a + size d) 0 !mine in
      let whole = List.fold_left (fun a d -> a + size d) 0 (left ()) in
      (* The largest claimant of what this cast needs. When it holds more
         than this worker does, this worker gives up its own claims and
         waits for that code rather than compiling the same closure again:
         the measurement of the first build showed fifteen workers each
         copying the whole closure of the other fourteen. The comparison
         is on sizes and pids, which both sides see, so exactly one worker
         of a group keeps its claims. *)
      let best = Hashtbl.fold (fun pid s acc -> match acc with
          | Some (_, s') when s' > s || (s' = s && pid > me) -> acc
          | Some _ | None -> Some (pid, s)) sizes None
      in
      match best with
      | Some (pid, s) when s > mine_size && s <= 2 * whole ->
        release ();
        mine := [];
        let w = wait_for (try Hashtbl.find files pid with Not_found -> []) in
        refresh_index ();
        reuse env sigma closure;
        mine := claim (left ());
        w
      | Some _ | None -> 0.
    in
    let left = left () in
    if CList.is_empty left then begin
      release ();
      (* r3-b instrumentation *)
      c_status := "reused";
      ConvLog.set_cache ~status:"reused" ~reused:!c_reused ~units:!c_units
        ~copied:0 ~copied_bytes:0 ~manifest_bytes:0
    end
    else begin
      let mine = !mine in
      (* The definitions the closure has linked to a unit that is not
         published: they are emitted again, so that the new unit refers
         only to published units. Their links come back if this unit
         fails before it is loaded. *)
      let stale = List.filter_map (fun d -> match definition_prefix env d with
          | Some p when Option.is_empty (unit_of_prefix p) -> Some (d, p)
          | Some _ | None -> None) closure
      in
      unlink_definitions env (List.map fst stale);
      let restore () =
        List.iter (fun (d, p) ->
            if not (definition_is_linked env d) then link_definitions env p [d]) stale
      in
      Fun.protect ~finally:(fun () -> release (); restore ()) @@ fun () ->
      let ml, prefix = Nativelib.cache_ml_filename () in
      let code, _symbols, upds =
        (* r3-b instrumentation *)
        ConvLog.with_unit_kind ConvLog.Dep (fun () ->
            ConvLog.time ConvLog.Codegen (fun () -> mk_deps_code env sigma prefix t1 t2))
      in
      let defs = definitions_of_updates upds in
      let keyed = List.filter_map (fun d -> match key env sigma d with
          | Some k -> Some (d, k)
          | None -> None) defs
      in
      if List.length keyed <> List.length defs then begin
        (* A definition without a key must not be advertised: compile the
           conversion the ordinary way. *)
        (try Sys.remove ml with Sys_error _ -> ());
        (* r3-b instrumentation *)
        c_status := "nokey";
        ConvLog.set_cache ~status:"nokey" ~reused:!c_reused ~units:!c_units
          ~copied:0 ~copied_bytes:0 ~manifest_bytes:0
      end else begin
        let copied = List.filter (fun d -> not (List.exists (definition_equal d) mine)) defs in
        c_copied := List.length copied;
        c_copied_bytes := List.fold_left (fun acc d -> acc + size d) 0 copied;
        let cmxs, parts =
          (* r3-b instrumentation *)
          ConvLog.with_unit_kind ConvLog.Dep (fun () ->
              Nativelib.compile_unit ~ml ~prefix code)
        in
        (* Each definition, with the prefix of the part that defines it. *)
        let part_of = List.concat_map (fun p ->
            List.map (fun d -> d, p.Nativelib.part_prefix) p.Nativelib.part_defs) parts in
        let keyed = List.map (fun (d, k) ->
            match List.find_opt (fun (d', _) -> definition_equal d d') part_of with
            | Some (_, p) -> d, k, p
            | None -> failwith ("no part of the unit defines " ^ definition_to_string d))
            keyed
        in
        let prefixes = prefix :: part_prefixes prefix parts in
        (* The units this one refers to: those holding the definitions of
           the closure this process has linked. A unit may be published
           only when every one of them is itself published; a definition
           linked by an ordinary conversion unit of this worker is not. *)
        let refs =
          List.fold_left (fun acc d -> match definition_prefix env d with
              | Some p when not (List.mem p prefixes) ->
                let u = Option.default p (unit_of_prefix p) in
                if List.mem u acc then acc else u :: acc
              | Some _ | None -> acc)
            [] closure
        in
        let publishable = List.for_all (fun p -> Hashtbl.mem units p) refs in
        let order = List.filter (fun p -> List.mem p refs) (List.rev !loaded_order) in
        (* Every load checks the file against its digest, the producer's
           own load included. *)
        let digest = Digest.to_hex (Digest.file cmxs) in
        if publishable && List.length order = List.length refs then
          publish env prefix cmxs ~digest ~parts keyed order
        else
          c_status := "private";
        if not (String.equal (Digest.to_hex (Digest.file cmxs)) digest) then
          failwith ("the unit " ^ cmxs ^ " changed after its compile");
        Nativelib.load_unit ~prefixes cmxs;
        List.iter (fun (d, _, p) -> link_definitions env p [d]) keyed;
        (* The unit is loaded here as a consumer's would be: a later cast
           of this worker whose new unit refers to it finds it in the load
           order, and can publish. *)
        loaded_order := prefix :: !loaded_order;
        (* r3-b instrumentation *)
        if not (String.equal !c_status "private") then
          c_status := (if !c_reused > 0 then "partial" else "compiled");
        ConvLog.set_cache ~status:!c_status ~reused:!c_reused ~units:!c_units
          ~copied:!c_copied ~copied_bytes:!c_copied_bytes ~manifest_bytes:!c_manifest_bytes
      end;
      ignore waited
    end
  end

(* Every path out of [prepare] resolves the claims this process holds:
   a waiter then stops at once. A failure here only costs the reuse: the
   conversion compiles what is not linked, as without a cache. *)
let prepare env t1 t2 =
  try prepare env t1 t2
  with e ->
    release ();
    if not (CErrors.noncritical e) then raise e;
    debug (fun () -> Pp.(str "cache: no unit: " ++ CErrors.print e))

(** {6 Setting up} *)

let remove_directory () =
  if not (Nativecode.keep_debug_files ()) then
    match Nativelib.cache_directory_made () with
    | None -> ()
    | Some d ->
      (try
         Array.iter (fun f -> try Sys.remove (d / f) with Sys_error _ -> ()) (Sys.readdir d);
         Unix.rmdir d
       with Unix.Unix_error _ | Sys_error _ -> ())

(* Half the processors the box has online, from /proc/cpuinfo; 1 when it
   cannot be read. *)
let half_the_cores () =
  let n =
    match open_in "/proc/cpuinfo" with
    | exception Sys_error _ -> 0
    | ch ->
      let rec count n = match input_line ch with
        | line ->
          let p = "processor" in
          let is_p = String.length line >= String.length p
                     && String.equal (String.sub line 0 (String.length p)) p in
          count (if is_p then n + 1 else n)
        | exception End_of_file -> n
      in
      Fun.protect ~finally:(fun () -> close_in ch) (fun () -> count 0)
  in
  max 1 (Stdlib.( / ) n 2)

let enable ?jobs () =
  if CheckWorkers.jobs () > 1 then begin
    enabled := true;
    main_pid := Unix.getpid ();
    cache_dir := Nativelib.cache_directory ();
    Nativelib.prepare_conversion := prepare;
    (* Every compile of the check, in the main process and in the
       workers, holds one of these slots while its compiler runs. *)
    Nativelib.slots := Some (!cache_dir, (match jobs with Some n -> n | None -> half_the_cores ()));
    (* Registered after [Nativelib]'s handler, so it runs before it: the
       directory goes before the temp dir that holds it. A worker ends
       with [Unix._exit], so only the main process removes it. *)
    at_exit (fun () -> if Unix.getpid () = !main_pid then remove_directory ())
  end

let is_enabled () = !enabled
