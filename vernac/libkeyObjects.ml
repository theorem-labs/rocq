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
open Libobject

(* Version 3 (S1b): the label blinds a constant's axiom-or-opaque-proof
   distinction (see [blind_constant]); versions 2 and 3 therefore never
   produce the same label for a library that has an opaque constant.
   Version 4 (BET-342): the plugin file digests of an ML-MODULE object and
   of an [ml_module] attempt are out of the key (vernac/mltop.ml,
   vernac/attempts.ml), so a plugin rebuilt from the same sources leaves
   the label of the libraries that declare it unchanged. *)
let version = 4

type summary = {
  name : DirPath.t;
  deps : (DirPath.t * Safe_typing.vodigest) array;
  safe_deps : DirPath.Set.t;
  info : Library_info.t;
}

exception No_view of string

(* Objects are viewed strictly in their order in the library: the syntax
   segment first, then the object segment, each in the order of its
   substitutive, keep and escape lists, each list from its head.
   [map_in_order] and the [let] sequences below fix that order, which
   [List.map] and tuples do not, so that the first object without a view is
   the one an error names. *)
let map_in_order f l = List.rev (List.rev_map f l)

let rec strip_object = function
  | ModuleObject (id, subs) -> ModuleObject (id, strip_substitutive subs)
  | ModuleTypeObject (id, subs) -> ModuleTypeObject (id, strip_substitutive subs)
  | IncludeObject alg -> IncludeObject (strip_algebraic alg)
  | KeepObject (id, { keep_objects }) ->
    KeepObject (id, { keep_objects = map_in_order strip_object keep_objects })
  | EscapeObject (id, { escape_objects }) ->
    EscapeObject (id, { escape_objects = map_in_order strip_object escape_objects })
  | ExportObject _ as o -> o
  | AtomicObject obj ->
    match interface_object obj with
    | Ok obj -> AtomicObject obj
    | Error what -> raise (No_view what)

and strip_substitutive (mbids, alg) = (mbids, strip_algebraic alg)

and strip_algebraic = function
  | Objs objs -> Objs (map_in_order strip_object objs)
  | Ref _ as r -> r

let strip_segment ((objs, { keep_objects }, { escape_objects }) : Declaremods.library_objects) =
  match
    let objs = map_in_order strip_object objs in
    let keep_objects = map_in_order strip_object keep_objects in
    let escape_objects = map_in_order strip_object escape_objects in
    (objs, { keep_objects }, { escape_objects })
  with
  | seg -> Ok (seg : Declaremods.library_objects)
  | exception No_view what -> Error what

(* The summary as the label reads it: names, digests and strings, so no
   source location and no file path. The record patterns name every field,
   and warning 9 (a field left out of a record pattern) is an error here:
   a field added to [summary], [UserWarn.t], [Deprecation.t] or
   [UserWarn.warn] stops the build until this view says how the label reads
   it. [DirPath.Set.elements] lists the set in [DirPath.compare] order (the
   set's own order), whatever the shape of its tree. *)
let[@warning "@9"] summary_view { name; deps; safe_deps; info = { UserWarn.depr; warn } } =
  let depr = Option.map (fun { Deprecation.since; note } -> (since, note)) depr in
  let warn = List.map (fun ({ UserWarn.note; cats } : UserWarn.warn) -> (note, cats)) warn in
  (name, Array.to_list deps, DirPath.Set.elements safe_deps, (depr, warn))

(* The axiom-or-opaque-proof blinding (design S1b, dispatch://INFRA-361).

   [blind_constant] maps a constant whose body is [Undef None] (an axiom or
   parameter with no body, as [Admitted] and [Axiom] make) and one whose body
   is [OpaqueDef _] (an opaque proof, as [Qed] makes) to the same canonical
   value [Undef None], keeping every other field of the record: the type, the
   universe context and constraints ([const_universes]), the typing and guard
   flags ([const_typing_flags]), the section data ([const_hyps],
   [const_univ_hyps]), the relevance, the inline mark and the bytecode
   descriptor ([const_body_code], which is already [Some BCconstant] for both,
   kernel/vmbytegen.ml:988). [Def] (a transparent body), [Primitive], [Symbol]
   and [Undef (Some _)] (an inlinable parameter, whose inline level a functor
   application observes) are left distinct.

   Exactness. A dependent of this library never observes the difference the
   blinding erases. The kernel's conversion gets no body for either form
   ([Environ.constant_value_in] raises [NotEvaluableConst] for both [OpaqueDef]
   and [Undef], and [evaluable_constant] is [false] for both:
   kernel/environ.ml:654-677); the VM and the native compiler both lower a use
   of either form to a plain constant reference (kernel/vmbytegen.ml:988-990,
   kernel/genlambda.ml:797-798). So neither conversion, nor the VM, nor native
   code unfolds an opaque constant any more than it unfolds an axiom, and a
   dependent compiled against one form type-checks, reduces and compiles
   identically against the other. The one observable the blinding drops -- the
   library's assumption set, which [Print Assumptions] reads -- is not carried
   by a dependent's object: the keep rule recomputes it from the current
   objects (its monotone axiom condition). The canonical value also drops the
   opaque table index of an [OpaqueDef (Indirect (_, _, dp, i))]; a dependent
   that embeds a foreign opaque reference into [dp] (a functor application or
   [Include] of this library's opaque proof) therefore has a label that no
   longer pins which proof index it reads, so the keep rule refuses to keep
   such a dependent across an edit that could move [dp]'s table
   ([foreign_opaque_libraries] below reports those [dp]). The kernel itself
   never applies this map; it is a view used only to compute the label. *)
let blind_constant (cb : Declarations.constant_body) : Declarations.constant_body =
  match cb.Declarations.const_body with
  | Declarations.Undef None | Declarations.OpaqueDef _ ->
    { cb with Declarations.const_body = Declarations.Undef None }
  | Declarations.Undef (Some _) | Declarations.Def _
  | Declarations.Primitive _ | Declarations.Symbol _ -> cb

let blind_compiled (compiled : Safe_typing.compiled_library) : Safe_typing.compiled_library =
  Safe_typing.replace_module_of_library compiled
    (Mod_declarations.map_constants blind_constant (Safe_typing.module_of_library compiled))

(* The report the keep rule needs beside the label (C1): per library, the
   constants whose contribution the label blinded, each with its current
   assumption status, and the other libraries this one holds a foreign opaque
   reference into. *)
type assumption_status = Axiom | Proof

type axiom_report = {
  blinded : (Constant.t * assumption_status) list;
  (** The blinded constants, ordered by [Constant.CanOrd.compare]. [Axiom] is
      a body of [Undef None] (no proof), [Proof] a body of [OpaqueDef _]. *)
  foreign_opaque_libraries : DirPath.Set.t;
  (** The libraries, other than this one, whose opaque table this library's
      compiled form holds an [Indirect] reference into. *)
}

(* The blinded constants of the module signature a dependent sees, with their
   names: the same walk the checker uses to enumerate a library's constants
   ([checker/mod_checking.ml] collect_constants_without_body). A functor
   signature ([MoreFunctor]) declares no constant a dependent names directly,
   so it contributes none. *)
let rec sig_blinded mp sign acc =
  match (sign : Mod_declarations.module_signature) with
  | Declarations.MoreFunctor _ -> acc
  | Declarations.NoFunctor struc ->
    List.fold_left (fun acc (lab, sfb) ->
        match (sfb : Mod_declarations.structure_field_body) with
        | Declarations.SFBconst cb ->
          (match cb.Declarations.const_body with
           | Declarations.Undef None -> (Constant.make2 mp lab, Axiom) :: acc
           | Declarations.OpaqueDef _ -> (Constant.make2 mp lab, Proof) :: acc
           | Declarations.Undef (Some _) | Declarations.Def _
           | Declarations.Primitive _ | Declarations.Symbol _ -> acc)
        | Declarations.SFBmodule mb ->
          sig_blinded (ModPath.MPdot (mp, lab)) (Mod_declarations.mod_type mb) acc
        | Declarations.SFBmind _ | Declarations.SFBrules _
        | Declarations.SFBmodtype _ -> acc)
      acc struc

(* Every library, other than [self], that a constant body of [mb] holds an
   opaque [Indirect] reference into. [map_constants] visits every constant of
   the module -- its signature, its interactive implementation and the module
   types of its functor parameters -- so an over-approximation here only makes
   the keep rule more conservative. *)
let foreign_opaque_of ~self mb =
  let acc = ref DirPath.Set.empty in
  let note cb =
    (match cb.Declarations.const_body with
     | Declarations.OpaqueDef o ->
       let (_, _, dp, _) = Opaqueproof.repr o in
       if not (DirPath.equal dp self) then acc := DirPath.Set.add dp !acc
     | Declarations.Undef _ | Declarations.Def _
     | Declarations.Primitive _ | Declarations.Symbol _ -> ());
    cb
  in
  let _ : Mod_declarations.module_body = Mod_declarations.map_constants note mb in
  !acc

let axiom_report ~(compiled : Safe_typing.compiled_library) : axiom_report =
  let self = Safe_typing.dirpath_of_library compiled in
  let mb = Safe_typing.module_of_library compiled in
  let blinded =
    List.sort (fun (a, _) (b, _) -> Constant.CanOrd.compare a b)
      (sig_blinded (ModPath.MPfile self) (Mod_declarations.mod_type mb) []) in
  { blinded; foreign_opaque_libraries = foreign_opaque_of ~self mb }

let label_result ~summary ~compiled ~syntax ~objects =
  match strip_segment syntax with
  | Error what -> Error ("syntax segment: " ^ what)
  | Ok syntax ->
    match strip_segment objects with
    | Error what -> Error ("object segment: " ^ what)
    | Ok objects ->
      let input =
        (version, blind_compiled compiled, syntax, objects, summary_view summary) in
      match Libkey.label (Obj.repr input) with
      | label -> Ok label
      | exception Libkey.Unsupported what -> Error ("encoding: " ^ what)

let label ~summary ~compiled ~syntax ~objects =
  Result.to_option (label_result ~summary ~compiled ~syntax ~objects)
