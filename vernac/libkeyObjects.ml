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
   the label of the libraries that declare it unchanged.
   Version 5 (D18 F1): the blinding covers only the constants of the
   library's own signature (the ones [axiom_report] lists); in a functor
   body, a module type and every other place an opaque proof stays one,
   distinct from an axiom, with its table index erased ([blind_compiled]),
   so an [Admitted -> Qed] edit there moves the label. *)
let version = 5

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

(* The axiom-or-opaque-proof blinding (design S1b, dispatch://INFRA-361;
   restricted to the library's own signature in version 5, D18 F1).

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

   Where. [blind_compiled] applies [blind_constant] only to the constants of
   the library's own signature ([map_own_signature]): its structure and the
   signature of each of its submodules, recursively, which are exactly the
   constants [axiom_report] lists with their current status. Every other
   constant body the compiled form holds -- in a functor's body, in the
   module type of a functor's parameter, in a module type, in the
   implementation of a sealed module -- keeps an opaque proof distinct from
   an axiom: its [OpaqueDef] is replaced by [unindexed_opaque], one fixed
   opaque body with no table index. Those forms are copied into a dependent's
   own declarations (a functor application copies its body's [Undef] or
   [OpaqueDef] into the applying library, kernel/mod_typing.ml; [Declare
   Module M : T] and [Module X : T := ...] copy a module type's), where they
   decide whether the dependent compiles ([Transparent R.c] fails on an opaque
   proof) and what its [Print Assumptions] says, while no report lists them,
   so the keep rule could not see an [Admitted -> Qed] edit there (review
   gate 1, F1). Such an edit therefore moves the label; a shift of the opaque
   table index alone still does not.

   Exactness. A dependent of this library never observes the difference the
   blinding erases, except through what the keep rule reads beside the label
   for exactly the constants [axiom_report] lists. The kernel's conversion
   gets no body for either form ([Environ.constant_value_in] raises
   [NotEvaluableConst] for both [OpaqueDef] and [Undef], and
   [evaluable_constant] is [false] for both: kernel/environ.ml:654-677); the
   VM and the native compiler both lower a use of either form to a plain
   constant reference (kernel/vmbytegen.ml:988-990,
   kernel/genlambda.ml:797-798). So neither conversion, nor the VM, nor native
   code unfolds an opaque constant any more than it unfolds an axiom, and a
   dependent compiled against one form type-checks, reduces and compiles
   identically against the other, but for three observables the label does
   not carry: a non-opaque strategy command on the constant, which errors on
   an opaque proof only, and an extraction of it, which warns (or, made an
   error, fails) on an axiom to realize or an opaque proof accessed (the keep
   rule compares the opacity the dependent's [keepfacts] recorded,
   [OpacityLog], with the status [axiom_report] gives now); an extraction
   with AccessOpaque (the default), which reads an opaque proof's BODY and
   extracts what it finds there, which no label covers (the hook logs each
   such read as an [opaque = true] query naming the library that holds the
   constant read; for a copy a module operation did not strengthen (a
   functor application, say) that is not the library whose opaque table the
   body came from,
   so the keep rule keeps the dependent only when the holder's object is
   byte-identical and so is the object of every library in the holder's
   registered [foreign_opaque_libraries] below); and the library's
   assumption set, which [Print Assumptions] reads (the keep rule recomputes
   it from the current objects: its monotone axiom condition). The status
   comparison and the assumption set read a constant's status off
   [axiom_report], which is why the blinding stops at the constants it lists;
   a body read reads no status, its check being byte-identity.
   The canonical value also drops the opaque table index of an [OpaqueDef
   (Indirect (_, _, dp, i))]; a dependent that embeds a foreign opaque
   reference into [dp] (a copy of this library's opaque proof that a module
   operation did not strengthen, a functor application, say) therefore has a
   label that no longer pins which proof index
   it reads, so the keep rule refuses to keep such a dependent across an edit
   that could move [dp]'s table ([foreign_opaque_libraries] below reports
   those [dp]). The kernel itself never applies this map; it is a view used
   only to compute the label. *)
let blind_constant (cb : Declarations.constant_body) : Declarations.constant_body =
  match cb.Declarations.const_body with
  | Declarations.Undef None | Declarations.OpaqueDef _ ->
    { cb with Declarations.const_body = Declarations.Undef None }
  | Declarations.Undef (Some _) | Declarations.Def _
  | Declarations.Primitive _ | Declarations.Symbol _ -> cb

(* The opaque body an opaque proof outside the own signature is read as: one
   fixed value, so no table index, and not [Undef None]. *)
let unindexed_opaque : (Constr.t, Opaqueproof.opaque, bool) Declarations.constant_def =
  Declarations.OpaqueDef (fst (Opaqueproof.create DirPath.empty Opaqueproof.empty_opaquetab))

let unindex_opaque (cb : Declarations.constant_body) : Declarations.constant_body =
  match cb.Declarations.const_body with
  | Declarations.OpaqueDef _ -> { cb with Declarations.const_body = unindexed_opaque }
  | Declarations.Undef _ | Declarations.Def _
  | Declarations.Primitive _ | Declarations.Symbol _ -> cb

(* [f] applied to each constant of the own signature [sign] of the module at
   [mp], with its name: the constants of its [NoFunctor] structure and, for
   each submodule, of the submodule's own signature, recursively. A functor
   signature ([MoreFunctor]) declares no constant a dependent names directly,
   and a module type ([SFBmodtype]) none at all, so neither is entered. This
   is the one walk both the blinding and [axiom_report] use, so the constants
   the label blinds are exactly the constants the report lists, and the same
   walk the checker uses to enumerate a library's constants
   ([checker/mod_checking.ml] collect_constants_without_body). *)
let rec map_own_signature f mp (sign : Mod_declarations.module_signature) =
  match sign with
  | Declarations.MoreFunctor _ -> sign
  | Declarations.NoFunctor struc ->
    Declarations.NoFunctor (List.map (fun (lab, sfb) ->
        match (sfb : Mod_declarations.structure_field_body) with
        | Declarations.SFBconst cb -> (lab, Declarations.SFBconst (f (Constant.make2 mp lab) cb))
        | Declarations.SFBmodule mb ->
          let sign = map_own_signature f (ModPath.MPdot (mp, lab)) (Mod_declarations.mod_type mb) in
          (lab, Declarations.SFBmodule (Mod_declarations.set_signature sign mb))
        | Declarations.SFBmind _ | Declarations.SFBrules _
        | Declarations.SFBmodtype _ -> (lab, sfb))
        struc)

let blind_compiled (compiled : Safe_typing.compiled_library) : Safe_typing.compiled_library =
  let self = ModPath.MPfile (Safe_typing.dirpath_of_library compiled) in
  let mb = Mod_declarations.map_constants unindex_opaque (Safe_typing.module_of_library compiled) in
  let sign = map_own_signature (fun _ cb -> blind_constant cb) self (Mod_declarations.mod_type mb) in
  Safe_typing.replace_module_of_library compiled (Mod_declarations.set_signature sign mb)

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
   names: the constants [map_own_signature] walks, so exactly the ones
   [blind_compiled] blinds. *)
let sig_blinded mp sign =
  let acc = ref [] in
  let note c (cb : Declarations.constant_body) =
    (match cb.Declarations.const_body with
     | Declarations.Undef None -> acc := (c, Axiom) :: !acc
     | Declarations.OpaqueDef _ -> acc := (c, Proof) :: !acc
     | Declarations.Undef (Some _) | Declarations.Def _
     | Declarations.Primitive _ | Declarations.Symbol _ -> ());
    cb
  in
  let _ : Mod_declarations.module_signature = map_own_signature note mp sign in
  !acc

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
      (sig_blinded (ModPath.MPfile self) (Mod_declarations.mod_type mb)) in
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
