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

let plugins () =
  List.map
    (fun p ->
       let name = Mltop.PluginSpec.to_package p in
       let files = match Mltop.PluginSpec.digest p with
         | ds -> List.map Digest.to_hex ds
         | exception Sys_error _ -> [ "unknown" ]
       in
       (name, String.concat "," files))
    (Mltop.get_loaded_modules ())

let load_order () =
  List.map (fun dir -> (DirPath.to_string dir, Library.library_digest dir)) (Library.loaded_libraries ())

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

(* Reads taken once, at each proof's start, for the channels that have no
   single read point (BET-84, census rows 2, 3, 4, 13, M3, M7). They are
   recorded as ordinary reads, so the matcher treats them like the rest. *)
let read_at_start () =
  if Proof_recorder.active () then begin
    let env = Global.env () in
    let one row channel what v =
      Proof_recorder.read ~row ~channel ~key:(fun () -> "")
        ~value:(fun () -> Some (Proof_recorder.digest ~what v))
    in
    one "2" "universe_graph" "universes" (Environ.universes env);
    one "2" "quality_graph" "qualities" (Environ.qualities env);
    one "3" "named_context" "named_context" (Environ.named_context env);
    one "3" "variable_opacity" "variable_opacity"
      (List.map (fun d -> let id = Context.Named.Declaration.get_id d in (id, Decls.variable_opacity id))
         (Environ.named_context env));
    one "4" "typing_flags" "typing_flags" (Environ.typing_flags env);
    one "13" "options" "options" (Goptions.get_tables ());
    one "13" "warnings" "warnings" (CWarnings.get_flags ());
    one "M3" "generalizable" "generalizable" (Implicit_quantifiers.generalizable_idents ());
    one "M7" "template_default_univs" "template_default_univs" (UState.template_default_univs ())
  end
