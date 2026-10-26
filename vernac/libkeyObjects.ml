(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Libobject

let version = 1

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

let label_result ~compiled ~syntax ~objects =
  match strip_segment syntax with
  | Error what -> Error ("syntax segment: " ^ what)
  | Ok syntax ->
    match strip_segment objects with
    | Error what -> Error ("object segment: " ^ what)
    | Ok objects ->
      match Libkey.label (Obj.repr (version, (compiled : Safe_typing.compiled_library), syntax, objects)) with
      | label -> Ok label
      | exception Libkey.Unsupported what -> Error ("encoding: " ^ what)

let label ~compiled ~syntax ~objects = Result.to_option (label_result ~compiled ~syntax ~objects)
