(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file in the root directory)               *)
(************************************************************************)

open Names
open Vernacexpr

(* The trusted driver loads this plugin only after loading the complete
   dependency closure.  Keep this snapshot outside Summary state: an untrusted
   vernacular command must not be able to enlarge or roll it back. *)
let bootstrap_libraries = Library.loaded_libraries ()

let reject ?loc reason =
  CErrors.user_err ?loc
    Pp.(str "Restricted model compilation rejects " ++ str reason ++ str ".")

let dirpath_of_qualid qid =
  let path, basename = Libnames.repr_qualid qid in
  Libnames.add_dirpath_suffix path basename

let dirpath_mem path paths =
  List.exists (DirPath.equal path) paths

let currently_authorized_libraries () =
  let loaded = Library.loaded_libraries () in
  List.filter (fun path -> dirpath_mem path loaded) bootstrap_libraries

let resolve_loaded_suffix ?loc qid =
  let suffix = dirpath_of_qualid qid in
  let matches =
    List.filter
      (fun path -> Libnames.is_dirpath_suffix_of suffix path)
      (currently_authorized_libraries ())
  in
  match matches with
  | [_] -> ()
  | [] ->
    reject ?loc
      ("Require of library " ^ Libnames.string_of_qualid qid ^
       ", which was not loaded by the trusted bootstrap")
  | _ ->
    reject ?loc
      ("ambiguous Require of library " ^ Libnames.string_of_qualid qid)

let resolve_loaded_from root qid =
  (* [From Coq] is a compatibility alias whose expansion depends on the
     requested library.  Restricting it to a unique already-loaded suffix is
     equivalent for our purpose and avoids duplicating the resolver's legacy
     alias table here. *)
  if String.equal (Libnames.string_of_qualid root) "Coq" then
    resolve_loaded_suffix ?loc:qid.CAst.loc qid
  else
    let full =
      Libnames.append_dirpath (dirpath_of_qualid root) (dirpath_of_qualid qid)
    in
    if not (dirpath_mem full (currently_authorized_libraries ())) then
      reject ?loc:qid.CAst.loc
        ("Require of library " ^ DirPath.to_string full ^
         ", which was not loaded by the trusted bootstrap")

let validate_require from qids =
  List.iter
    (fun qid ->
      match from with
      | None -> resolve_loaded_suffix ?loc:qid.CAst.loc qid
      | Some root -> resolve_loaded_from root qid)
    qids

let rec contains_bypass_check flags =
  List.exists
    (fun { CAst.v = key, value; _ } ->
      String.equal key "bypass_check" ||
      match value with
      | Attributes.VernacFlagList nested -> contains_bypass_check nested
      | Attributes.VernacFlagEmpty | Attributes.VernacFlagLeaf _ -> false)
    flags

let is_kernel_checking_option = function
  | ["Guard"; "Checking"]
  | ["Positivity"; "Checking"]
  | ["Universe"; "Checking"] -> true
  | _ -> false

let is_allowed_proof_extension { ext_plugin; ext_entry; ext_index } =
  match ext_plugin, ext_entry, ext_index with
  (* Ordinary Ltac proof sentences are routed through this vernacular adapter.
     The tactic expression itself remains standard Rocq behavior. *)
  | "rocq-runtime.plugins.ltac", "VernacSolve", 0 -> true
  (* Ltac2 has the same shape.  Its second branch and Ltac's parallel adapter
     launch parallel proof work, so the initial policy deliberately omits them. *)
  | "rocq-runtime.plugins.ltac2", "VernacLtac2", 0 -> true
  | _ -> false

let validate_controls controls =
  List.iter
    (fun { CAst.v; loc } ->
      match v with
      | ControlRedirect _ -> reject ?loc "the Redirect control"
      | ControlProfile (Some _) -> reject ?loc "file-backed profiling"
      | ControlTime | ControlInstructions | ControlProfile None
      | ControlTimeout _ | ControlFail | ControlSucceed -> ())
    controls

let validate_synterp ?loc = function
  | VernacLoad _ -> reject ?loc "Load"
  | VernacDeclareMLModule _ -> reject ?loc "Declare ML Module"
  | VernacChdir _ -> reject ?loc "Chdir"
  | VernacExtraDependency _ -> reject ?loc "Extra Dependency"
  | VernacExtend (extension, _) when is_allowed_proof_extension extension -> ()
  | VernacExtend ({ ext_plugin; ext_entry; ext_index }, _) ->
      reject ?loc
        (Printf.sprintf "vernacular extension %s:%s:%d"
           ext_plugin ext_entry ext_index)
  | VernacSetOption (_, option_name, _) when is_kernel_checking_option option_name ->
    reject ?loc ("changes to " ^ String.concat " " option_name)
  | VernacSafeRequire (from, _, qids) -> validate_require from qids
  | VernacRequire (from, _, qids) -> validate_require from (List.map fst qids)
  | VernacReservedNotation _ | VernacNotation _ | VernacDeclareCustomEntry _
  | VernacBeginSection _ | VernacEndSegment _ | VernacImport _
  | VernacDeclareModule _ | VernacDefineModule _ | VernacDeclareModuleType _
  | VernacInclude _ | VernacSetOption _ | VernacProofMode _ -> ()

let validate_synpure ?loc = function
  | VernacPrint (PrintUniverses { file = Some _; _ }) ->
    reject ?loc "file output from Print Universes"
  | VernacResetName _ | VernacResetInitial | VernacBack _
  | VernacUndo _ | VernacUndoTo _ ->
    reject ?loc "document-state rollback"
  | _ -> ()

let validate ({ CAst.v = { control; attrs; expr }; loc } : vernac_control) _ =
  validate_controls control;
  if contains_bypass_check attrs then reject ?loc "the bypass_check attribute";
  match expr with
  | VernacSynterp command -> validate_synterp ?loc command
  | VernacSynPure command -> validate_synpure ?loc command

let () = Stm.document_add_hook validate
