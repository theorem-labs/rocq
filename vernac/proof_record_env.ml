(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(* The running executable is one file for the whole compile. *)
let binary_digest =
  lazy (match Digest.file Sys.executable_name with
      | d -> Digest.to_hex d
      | exception Sys_error _ -> "unknown")

(* A plugin's files do not change during a compile, so each is hashed once,
   not at every proof's start. *)
let plugin_digests : (string, string) Hashtbl.t = Hashtbl.create 16

let plugins () =
  List.map
    (fun p ->
       let name = Mltop.PluginSpec.to_package p in
       match Hashtbl.find_opt plugin_digests name with
       | Some d -> (name, d)
       | None ->
         let files = match Mltop.PluginSpec.digest p with
           | ds -> List.map Digest.to_hex ds
           | exception Sys_error _ -> [ "unknown" ]
         in
         let d = String.concat "," files in
         Hashtbl.add plugin_digests name d;
         (name, d))
    (Mltop.get_loaded_modules ())

let load_order () =
  List.map (fun dir -> (DirPath.to_string dir, Library.library_digest dir)) (Library.loaded_libraries ())

(* The kernel records a constant of a required library by that library's .vo
   digest, not by its body. It asks once for each library, so the walk of the
   loaded ones is not a cost. The library being compiled has no digest, so its
   own constants are digested. *)
let () = Proof_recorder.set_library_digest (fun name ->
    match List.find_opt (fun dir -> String.equal (DirPath.to_string dir) name)
            (Library.loaded_libraries ()) with
    | None -> None
    | Some dir ->
      match Library.library_digest dir with
      | "unknown" -> None
      | d -> Some d)

(* [toolchain] runs at the start of every proof, for that proof's
   [toolchain_key]. Rebuilt at each call it walks every loaded library for
   its .vo digest, rebuilds the plugin list and reads the stack rlimit from
   /proc, and it hands back three brand-new lists, which no memo downstream
   can recognise. So keep the last record and return THE SAME PHYSICAL VALUE
   while the state it reads has not moved.

   The detector is the loaded-library list, the loaded-plugin list and the
   warning flags. It is sound for every field:
   - [binary] and [stack_limit] are properties of the running process, fixed
     for the whole compile;
   - [plugins] is a function of the loaded-plugin list alone (a plugin's
     files are hashed once, in [plugin_digests]);
   - [load_order] is a function of the loaded-library list alone: a library
     is interned and registered once ([Library]'s [intern_library] returns at
     once for a library that is already loaded), so the .vo digest of a
     listed library cannot move;
   - [safe_deps] is a function of the same list, for the same reason: a
     library's mode (full or safe) is fixed at that one registration, and a
     later [Require] of a loaded library registers nothing;
   - [warnings] is the one field that moves on its own ([Set Warnings]), and
     it is compared directly.
   The two lists are compared element by element and allocate nothing, so an
   added, a dropped and a reordered entry are all caught: the detector does
   not rest on the assumption that a compile only adds. *)
let same_plugin p q =
  String.equal (Mltop.PluginSpec.to_package p) (Mltop.PluginSpec.to_package q)

let toolchain_cache
  : (DirPath.t list * Mltop.PluginSpec.t list * string * Proof_record.toolchain) option ref
  = ref None

let toolchain () : Proof_record.toolchain =
  let libs = Library.loaded_libraries () in
  let mods = Mltop.get_loaded_modules () in
  let warnings = CWarnings.get_flags () in
  match !toolchain_cache with
  | Some (libs0, mods0, warnings0, tc)
    when String.equal warnings0 warnings
      && List.equal DirPath.equal libs0 libs
      && List.equal same_plugin mods0 mods -> tc
  | Some _ | None ->
    let tc : Proof_record.toolchain = Proof_record.{
        binary = Lazy.force binary_digest;
        plugins = plugins ();
        load_order = load_order ();
        warnings;
        safe_deps = List.map DirPath.to_string (Library.safe_loaded_libraries ());
        stack_limit = Proof_limits.rlimit "Max stack size";
      } in
    toolchain_cache := Some (libs, mods, warnings, tc);
    tc

(* [position] is built at the start of every proof, with the recorder on or
   off, and [Lib.current_dirpath] counts the open sections by walking the
   whole library stack, which grows with the file. Both fields are a function
   of [Lib.cwd ()] alone: a section or a module opens by adding a suffix to
   the path prefix and closes by restoring the prefix it saved, so the same
   PHYSICAL path prefix carries the same open sections. Keep the last record
   and return it while that prefix has not moved. A prefix that is rebuilt
   equal costs a rebuild, not a wrong answer. *)
let position_cache : (Libnames.full_path * Proof_record.position) option ref = ref None

let position () =
  let path = Lib.cwd () in
  match !position_cache with
  | Some (path0, p) when path0 == path -> p
  | Some _ | None ->
    let p = Proof_record.{
        (* [cwd] is the module path with the open sections. The matcher joins
           against the .glob name, whose third column is
           [Lib.current_dirpath false], so [module_path] is that path and
           [section_path] adds the open sections. *)
        module_path = DirPath.to_string (Lib.current_dirpath false);
        section_path = Libnames.string_of_path path;
      } in
    position_cache := Some (path, p);
    p

let qualities_slot = Proof_recorder.slot ()
let named_slot = Proof_recorder.slot ()
let flags_slot = Proof_recorder.slot ()
let generalizable_slot = Proof_recorder.slot ()
let template_slot = Proof_recorder.slot ()
let universe_slot = Proof_recorder.slot ()

let cached slot what v = Proof_recorder.digest_slot slot ~what v

(* Row 2, the global universe graph. A proof reads it through every query on
   a graph built from it: the global graph itself, and the proof's private
   graph G ∪ L, where L holds the constraints the statement and the tactics
   added. One edited file earlier adds levels and constraints, so a digest of
   the whole graph made every later proof miss.

   The proof's footprint T is every level that any graph operation names
   while the proof is recorded: each check, and each enforce or add, which
   makes the endpoints of every local edge part of T. A path in G ∪ L
   between two levels of a query alternates between global segments and
   edges of L, and every segment has its two ends in T. So every answer is a
   function of L and of the order G induces on T. The recorded value is that
   order: for each ordered pair of global levels of T, whether G proves a
   strict, a non-strict or no constraint. By induction over the proof's steps,
   equal answers give the same L and the same term. The statement's own
   universe state, the base case, is in the statement key ([Declare]).

   Levels of T that are not global at the proof's start are left out when
   this proof made them: their names carry this library and a counter past
   the counter at the start, which the row 18 read pins, so no global level
   of a replaying compile can have that name. Any other undeclared level stays
   in the key, and replay requires it still undeclared. A query that reads
   the whole global graph, or a footprint too large to compare pairwise,
   records the digest of the whole graph instead. *)
type universe_frame = {
  start_graph : UGraph.t;
  start_counter : int;
  library : Names.DirPath.t;
  mutable touched : Univ.Level.Set.t;
  mutable whole : bool;
}

type universe_footprint = {
  whole_graph : bool;
  declared : Univ.Level.t list;
  undeclared : Univ.Level.t list;
}

(* Pairwise comparison is quadratic; past this size the whole graph is read. *)
let universe_pairs_limit = 64

let universe_frames : universe_frame list ref = ref []

let touch levels =
  List.iter (fun f ->
      if not (Univ.Level.Set.subset levels f.touched) then
        f.touched <- Univ.Level.Set.union levels f.touched)
    !universe_frames

let note_universe_query graph query =
  if Proof_recorder.active () then
    match query with
    | UGraph.Constraints levels | UGraph.Declared levels -> touch levels
    | UGraph.Type_in_type -> ()
    | UGraph.Domain | UGraph.All_constraints | UGraph.Graph | UGraph.Opaque _ ->
      let global = Environ.universes (Global.env ()) in
      if graph == global || List.exists (fun f -> graph == f.start_graph) !universe_frames then
        List.iter (fun f -> f.whole <- true) !universe_frames
      else
        (* A private graph: every level in it may be read. When it was built
           from the global graph this is every global level, and the
           footprint passes the pairwise limit. *)
        touch (UGraph.without_query_hook (fun () -> UGraph.domain graph))

let made_by_this_proof f l =
  match Univ.Level.name l with
  | None -> false
  | Some g ->
    let library, worker, n = Univ.UGlobal.repr g in
    String.equal worker "" && n > f.start_counter && Names.DirPath.equal library f.library

let footprint_of f =
  let undeclared =
    match UGraph.check_declared_universes f.start_graph f.touched with
    | Ok () -> Univ.Level.Set.empty
    | Error missing -> missing
  in
  let declared = Univ.Level.Set.diff f.touched undeclared in
  let undeclared = Univ.Level.Set.filter (fun l -> not (made_by_this_proof f l)) undeclared in
  let whole_graph = f.whole || Univ.Level.Set.cardinal declared > universe_pairs_limit in
  if whole_graph then { whole_graph; declared = []; undeclared = [] }
  else { whole_graph;
         declared = Univ.Level.Set.elements declared;
         undeclared = Univ.Level.Set.elements undeclared }

(* The key in text, short enough not to grow the record: ["w"] for the whole
   graph, else ["f"], then the declared and the undeclared levels on two
   lines. A line lists [S] (Set), [V<n>] (a bound variable) and, per
   library and process, [G<dirpath>|<process>|<n>,<n>...], separated by
   [;]. A key that does not read back is not taken for another: the proof
   misses. *)
let encode_levels levels =
  let groups = Hashtbl.create 8 and order = ref [] and others = ref [] in
  List.iter (fun l ->
      match Univ.Level.name l, Univ.Level.var_index l with
      | Some g, _ ->
        let dp, s, n = Univ.UGlobal.repr g in
        let k = (Names.DirPath.to_string dp, s) in
        (match Hashtbl.find_opt groups k with
         | Some ns -> Hashtbl.replace groups k (n :: ns)
         | None -> Hashtbl.add groups k [ n ]; order := k :: !order)
      | None, Some i -> others := ("V" ^ string_of_int i) :: !others
      | None, None -> others := "S" :: !others)
    levels;
  let group (dp, s) =
    let ns = List.rev (Hashtbl.find groups (dp, s)) in
    Printf.sprintf "G%s|%s|%s" dp s (String.concat "," (List.map string_of_int ns))
  in
  String.concat ";" (List.rev_append !others (List.rev_map group !order))

let decode_levels line =
  let dirpath s = Names.DirPath.make (List.rev_map Names.Id.of_string (String.split_on_char '.' s)) in
  let item it =
    if String.equal it "S" then [ Univ.Level.set ]
    else if String.length it > 1 && it.[0] = 'V' then
      [ Univ.Level.var (int_of_string (String.sub it 1 (String.length it - 1))) ]
    else if String.length it > 1 && it.[0] = 'G' then
      match String.split_on_char '|' (String.sub it 1 (String.length it - 1)) with
      | [ dp; s; ns ] ->
        let dp = dirpath dp in
        List.map (fun n -> Univ.Level.make (Univ.UGlobal.make dp s (int_of_string n)))
          (String.split_on_char ',' ns)
      | _ -> failwith "universe footprint group"
    else failwith "universe footprint item"
  in
  if String.equal line "" then [] else List.concat_map item (String.split_on_char ';' line)

let universe_footprint_key fp =
  if fp.whole_graph then "w"
  else "f\n" ^ encode_levels fp.declared ^ "\n" ^ encode_levels fp.undeclared

let universe_footprint_of_key key =
  match String.split_on_char '\n' key with
  | [ "w" ] -> Some { whole_graph = true; declared = []; undeclared = [] }
  | [ "f"; d; u ] ->
    (match decode_levels d, decode_levels u with
     | declared, undeclared -> Some { whole_graph = false; declared; undeclared }
     | exception (Failure _ | Invalid_argument _ | CErrors.UserError _) -> None)
  | _ -> None

(* The order is computed with universe checking ON, whatever the graph's
   own mode: a graph that does not check ([Unset Universe Checking]) proves
   every constraint, while the proof can check its own constraints against
   it ([#[bypass_check(universes=no)]]), so the order the proof's checks see
   is the checked one. The graph's mode is kept in the value beside it
   (fixture universe_checked_proof_unchecked_graph). *)
let universe_footprint_value graph fp =
  UGraph.without_query_hook (fun () ->
      if fp.whole_graph then cached universe_slot "universe_graph" graph
      else
        let declared_now =
          let declared = List.fold_left (fun s l -> Univ.Level.Set.add l s) Univ.Level.Set.empty fp.declared in
          Result.is_ok (UGraph.check_declared_universes graph declared)
        in
        let undeclared_now =
          List.for_all (fun l ->
              Result.is_error (UGraph.check_declared_universes graph (Univ.Level.Set.singleton l)))
            fp.undeclared
        in
        if not (declared_now && undeclared_now) then "universe_domain_changed"
        else
          let checked = UGraph.set_type_in_type false graph in
          let levels = Array.of_list (List.sort Univ.Level.compare fp.declared) in
          let n = Array.length levels in
          let order = Bytes.make (n * n) '.' in
          for i = 0 to n - 1 do
            for j = 0 to n - 1 do
              if i <> j then
                let a = levels.(i) and b = levels.(j) in
                let c =
                  if UGraph.check_constraint checked (a, Univ.UnivConstraint.Lt, b) then 'l'
                  else if UGraph.check_constraint checked (a, Univ.UnivConstraint.Le, b) then 'e'
                  else '-'
                in
                Bytes.set order (i * n + j) c
            done
          done;
          Proof_recorder.digest ~what:"universe_order"
            (UGraph.type_in_type graph, UGraph.above_prop_qvars graph, Bytes.to_string order))

let record_universe_footprint () =
  if Proof_recorder.active () then
    match !universe_frames with
    | f :: _ ->
      let fp = footprint_of f in
      let key = universe_footprint_key fp in
      let value = Some (universe_footprint_value f.start_graph fp) in
      Proof_recorder.read ~row:"2" ~channel:"universe_constraint" ~key:(fun () -> key)
        ~value:(fun () -> value)
    | [] ->
      (* The stack follows the recorder's open proofs, so this is not
         expected; without a footprint the proof must run. *)
      Proof_recorder.ineligible ~reason:"universe_footprint_missing"
        ~detail:"no universe footprint for the open proof"

let set_universe_frames frames =
  universe_frames := frames;
  UGraph.set_query_hook (match frames with [] -> None | _ :: _ -> Some note_universe_query)

let drop_universe_frame () =
  match !universe_frames with
  | _ :: rest -> set_universe_frames rest
  | [] -> ()

let drop_universe_frames () =
  match !universe_frames with
  | [] -> ()
  | _ :: _ -> set_universe_frames []

(* Reads taken once, at each proof's start, for the channels that have no
   single read point (BET-84, census rows 2, 3, 4, 13, M3, M7). They are
   recorded as ordinary reads, so the matcher treats them like the rest.
   Replay evaluates the same list at the proof it is about to replay
   (`Proof_replay_env`), so the two sides can never drift apart. *)
let start_reads () =
  let env = Global.env () in
  let one row channel value = Proof_record.{ row; channel; key = ""; value = Some (value ()) } in
  let named = Environ.named_context env in
  [
    one "2" "quality_graph" (fun () -> cached qualities_slot "qualities" (Environ.qualities env));
    one "3" "named_context" (fun () -> cached named_slot "named_context" named);
    one "3" "variable_opacity" (fun () ->
        Proof_recorder.digest ~what:"variable_opacity"
          (List.map (fun d -> let id = Context.Named.Declaration.get_id d in (id, Decls.variable_opacity id))
             named));
    one "4" "typing_flags" (fun () -> cached flags_slot "typing_flags" (Environ.typing_flags env));
    one "13" "options" (fun () -> Proof_recorder.digest ~what:"options" (Goptions.get_tables ()));
    one "13" "warnings" (fun () -> Proof_recorder.digest ~what:"warnings" (CWarnings.get_flags ()));
    one "M3" "generalizable" (fun () ->
        cached generalizable_slot "generalizable" (Implicit_quantifiers.generalizable_idents ()));
    one "M7" "template_default_univs" (fun () ->
        cached template_slot "template_default_univs" (UState.template_default_univs ()));
  ]

(* One footprint per proof the recorder holds open, recorded or not, so the
   stack and the recorder's open proofs stay aligned through nesting. *)
let read_at_start () =
  if Proof_recorder.writing () then begin
    let frame = {
      start_graph = Environ.universes (Global.env ());
      start_counter = fst (UnivGen.counters ());
      library = Global.current_dirpath ();
      touched = Univ.Level.Set.empty;
      whole = false;
    } in
    set_universe_frames (frame :: !universe_frames)
  end;
  if Proof_recorder.active () then begin
    List.iter
      (fun Proof_record.{ row; channel; key; value } ->
         Proof_recorder.read ~row ~channel ~key:(fun () -> key) ~value:(fun () -> value))
      (start_reads ())
  end
