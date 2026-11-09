(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ

let import senv opac clib vmtab digest =
  let senv = Safe_typing.check_flags_for_library clib senv in
  let dp = Safe_typing.dirpath_of_library clib in
  let mb = Safe_typing.module_of_library clib in
  let env = Safe_typing.env_of_safe_env senv in
  let qualities, univs = Safe_typing.univs_of_library clib in
  let check_quality q =
    Sorts.QVar.is_global q &&
    not (QGraph.is_declared (Sorts.Quality.QVar q) (Environ.qualities env))
  in
  let () = assert (Sorts.QVar.Set.for_all check_quality (fst qualities)) in
  let env = push_qualities ~rigid:true qualities env in
  let env = push_context_set ~strict:true univs env in
  let env = Modops.add_retroknowledge (Mod_declarations.mod_retroknowledge mb) env in
  let env = Environ.link_vm_library vmtab env in
  let opac = Mod_checking.check_module env opac (Names.ModPath.MPfile dp) mb in
  let (_,senv) = Safe_typing.import clib vmtab digest senv in senv, opac

let import senv opac clib vmtab digest : _ * _ =
  NewProfile.profile "import"
    ~args:(fun () ->
        let dp = Safe_typing.dirpath_of_library clib in
        [("name", `String (Names.DirPath.to_string dp))])
    (fun () ->import senv opac clib vmtab digest)
    ()

(* An admitted library is loaded without being checked, so it may not take
   part in a merge, in either direction: neither side of a comparison
   against declarations nobody re-derived means anything. *)
let unsafe_import senv clib vmtab digest =
  Indmerge.set_admitted true;
  let (_, senv) =
    try Safe_typing.import clib vmtab digest senv
    with e -> Indmerge.set_admitted false; raise e
  in
  Indmerge.set_admitted false;
  senv
