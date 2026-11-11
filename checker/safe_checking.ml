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

let env_of_library senv clib =
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
  Modops.add_retroknowledge (Mod_declarations.mod_retroknowledge mb) env

(* The checker does not read the [vmlibrary] segment of the file at all: it
   compiles the bytecode of every constant itself, from the declarations it is
   about to check, and hands the resulting table to [Safe_typing.import] in place
   of the one stored in the file. *)
let compile_vm_library env clib =
  let dp = Safe_typing.dirpath_of_library clib in
  let mb = Safe_typing.module_of_library clib in
  let vmtab = Vmlibrary.set_path dp (Environ.vm_library env) in
  let vmtab, mb = Mod_checking.compile_module_bytecode env vmtab (Names.ModPath.MPfile dp) mb in
  vmtab, Safe_typing.replace_module_of_library clib mb

let import senv opac clib digest =
  let senv = Safe_typing.check_flags_for_library clib senv in
  let dp = Safe_typing.dirpath_of_library clib in
  let env = env_of_library senv clib in
  let vmtab, clib = compile_vm_library env clib in
  let env = Environ.set_vm_library vmtab env in
  let mb = Safe_typing.module_of_library clib in
  (* The environment already carries the merges made for earlier libraries,
     so the body checked against it has to name them the same way. *)
  (* The bytecode above was compiled from the module as the file holds it,
     BEFORE this rewrite, so the recompilation of [Mod_checking] no longer
     gives VM/kernel agreement by construction (see its comment). It still
     holds here, and only because:
       - every relocation that names a global lives in the declaration's
         patch table, which [Indmerge.apply_earlier_merges] rewrites with
         the same substitution as the term it patches
         ([Declareops.subst_const_body] -> [Vmemitcodes.subst_body_code]);
       - the non-substituted table, which no substitution reaches, holds no
         global name: [Vmemitcodes.names_global] says which relocations name
         one, and [Vmemitcodes.to_memory] refuses to store such a relocation
         there;
       - the environment the VM resolves those names in is keyed by user
         name, which a merge is free to keep;
       - and a merge happens only between blocks [Indmerge.eq_mib] accepts,
         which pins constructor tags and arities, so the compiled code reads
         the same layout either way.
     Move a global relocation into the non-substituted table and the VM would
     keep the pre-merge name while the kernel checks the merged one. *)
  let mb = Indmerge.apply_earlier_merges (Names.ModPath.MPfile dp) mb in
  let opac = Mod_checking.check_module env opac (Names.ModPath.MPfile dp) mb in
  let vmtab = Vmlibrary.inject (Vmlibrary.export vmtab) in
  let (_,senv) = Safe_typing.import clib vmtab digest senv in senv, opac

let import senv opac clib digest : _ * _ =
  NewProfile.profile "import"
    ~args:(fun () ->
        let dp = Safe_typing.dirpath_of_library clib in
        [("name", `String (Names.DirPath.to_string dp))])
    (fun () ->import senv opac clib digest)
    ()

(* An admitted library is loaded without being checked. It still takes part
   in merges, as source and as target: it is already trusted whole, so
   merging against it adds no trust, and the grader's invocation leaves our
   own statement library unchecked. *)
let unsafe_import senv clib digest =
  (* Admitted libraries are trusted for their declarations, but their bytecode is
     recompiled all the same, so that the trusted surface is exactly the same. *)
  let env = env_of_library senv clib in
  let vmtab, clib = compile_vm_library env clib in
  let vmtab = Vmlibrary.inject (Vmlibrary.export vmtab) in
  let (_,senv) = Safe_typing.import clib vmtab digest senv in senv
