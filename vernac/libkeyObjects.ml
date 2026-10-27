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

let version = 2

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

let label_result ~summary ~compiled ~syntax ~objects =
  match strip_segment syntax with
  | Error what -> Error ("syntax segment: " ^ what)
  | Ok syntax ->
    match strip_segment objects with
    | Error what -> Error ("object segment: " ^ what)
    | Ok objects ->
      let input =
        (version, (compiled : Safe_typing.compiled_library), syntax, objects, summary_view summary) in
      match Libkey.label (Obj.repr input) with
      | label -> Ok label
      | exception Libkey.Unsupported what -> Error ("encoding: " ^ what)

let label ~summary ~compiled ~syntax ~objects =
  Result.to_option (label_result ~summary ~compiled ~syntax ~objects)
