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

let toolchain () : Proof_record.toolchain = Proof_record.{
    binary = Lazy.force binary_digest;
    plugins = plugins ();
    load_order = load_order ();
    warnings = CWarnings.get_flags ();
    safe_deps = List.map DirPath.to_string (Library.safe_loaded_libraries ());
    stack_limit = Proof_limits.rlimit "Max stack size";
  }

let position () = Proof_record.{
    (* [cwd] is the module path with the open sections. The matcher joins
       against the .glob name, whose third column is
       [Lib.current_dirpath false], so [module_path] is that path and
       [section_path] adds the open sections. *)
    module_path = DirPath.to_string (Lib.current_dirpath false);
    section_path = Libnames.string_of_path (Lib.cwd ());
  }

(* A value of the global state that no proof changes in place, digested again
   only when it is a different value: the universe graph is one value from
   one declaration to the next, so most proofs reuse the last digest. *)
let slot () = ref None

let cached slot what v =
  match !slot with
  | Some (o, d) when o == Obj.repr v -> d
  | Some _ | None ->
    let d = Proof_recorder.digest ~what v in
    slot := Some (Obj.repr v, d);
    d

let universes_slot = slot ()
let qualities_slot = slot ()
let named_slot = slot ()
let flags_slot = slot ()
let generalizable_slot = slot ()
let template_slot = slot ()

(* Reads taken once, at each proof's start, for the channels that have no
   single read point (BET-84, census rows 2, 3, 4, 13, M3, M7). They are
   recorded as ordinary reads, so the matcher treats them like the rest. *)
let read_at_start () =
  if Proof_recorder.active () then begin
    let env = Global.env () in
    let one row channel value =
      Proof_recorder.read ~row ~channel ~key:(fun () -> "") ~value:(fun () -> Some (value ()))
    in
    let named = Environ.named_context env in
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
        cached template_slot "template_default_univs" (UState.template_default_univs ()))
  end
