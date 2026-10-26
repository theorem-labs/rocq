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

(* A value of the global state that no proof changes in place, digested again
   only when it is a different value: the universe graph is one value from
   one declaration to the next, so most proofs reuse the last digest. *)
let universes_slot = Proof_recorder.slot ()
let qualities_slot = Proof_recorder.slot ()
let named_slot = Proof_recorder.slot ()
let flags_slot = Proof_recorder.slot ()
let generalizable_slot = Proof_recorder.slot ()
let template_slot = Proof_recorder.slot ()

let cached slot what v = Proof_recorder.digest_slot slot ~what v

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
    one "2" "universe_graph" (fun () -> cached universes_slot "universes" (Environ.universes env));
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

let read_at_start () =
  if Proof_recorder.active () then
    List.iter
      (fun Proof_record.{ row; channel; key; value } ->
         Proof_recorder.read ~row ~channel ~key:(fun () -> key) ~value:(fun () -> value))
      (start_reads ())
