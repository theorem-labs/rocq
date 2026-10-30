(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** What a module's implementation declares, where the environment holds an
    interface instead.

    [Module M : T := E] and [Module M : T. ... End M] put T in the
    environment, so a field T declares as a parameter has no body there even
    where E or the structure defines it. The summary's Axioms section reads
    "no body" as "assumed", and so reported a definition as an axiom
    (dispatch://BET-245): for [Module Asc : U := Plain] with
    [Definition q := Asc.p], [rocqchk -o] printed Seal2.Asc.p while
    [Print Assumptions] on a proof that uses it reads "Closed under the
    global context".

    [defines_constant] answers the one question that tells the two apart, the
    way [Print Assumptions] answers it ([lookup_constant_in_impl] in
    vernac/assumptions.ml): it resolves the constant's module path through
    the implementations the environment holds and reads whether the
    implementation gives that field a body. The substitutions
    vernac/assumptions.ml applies are not needed here, because they rename
    what is found and no renaming changes whether a field has a body.

    Every answer it is unsure of is [false], which keeps the name its caller
    would print. It reads an implementation and never a type: a module type
    can carry [Module M : T := E] of its own, and a module declared with
    [Declare Module] carries nothing else, while neither says what an
    implementation of it binds. *)

open Names
open Declarations
open Mod_declarations

(* What one module's implementation declares, read by label: the modules
   under it, which the walk goes through, and whether each constant has a
   body, which is the answer it is after. *)
type fields = {
  modules : module_body Id.Map.t;
  constants : bool Id.Map.t;
}

let no_fields = { modules = Id.Map.empty; constants = Id.Map.empty }

let fields_of_structure struc =
  let add fields (lab, field) = match field with
    | SFBconst cb ->
      { fields with
        constants = Id.Map.add lab (Declareops.constant_has_body cb) fields.constants }
    | SFBmodule msb -> { fields with modules = Id.Map.add lab msb fields.modules }
    | SFBmind _ | SFBrules _ | SFBmodtype _ -> fields
  in
  List.fold_left add no_fields struc

let lookup_module env mp =
  match Environ.lookup_module mp env with
  | mb -> Some mb
  | exception Not_found -> None

(* Each module path is read once for each environment that asks about it: the
   summary asks about every constant it would print and about every module on
   the way to one, and an alias chain asks for the same structure again at
   each of its links. The environment is compared by identity, as the memo of
   Print Assumptions is (sync_memo in vernac/assumptions.ml), since what a
   path resolves to depends on it. A path that cannot be read is kept as the
   empty record, which answers for every label as a structure without that
   label does. *)
let memo = ref None

let read_memo env =
  match !memo with
  | Some (env', read) when env' == env -> read
  | Some _ | None -> ModPath.Map.empty

let keep_fields env paths fields =
  let read = List.fold_left (fun read mp -> ModPath.Map.add mp fields read)
      (read_memo env) paths
  in
  memo := Some (env, read);
  fields

(* An alias is followed as a loop, over the paths read so far, and not as a
   call: a chain of them is as long as a library cares to make it, and each
   of its links is given the fields the chain ends at. A link whose target
   lies under a module that is itself read through another alias is the one
   case that keeps a frame, since that module is read first; the modules such
   a chain needs are nested as deeply as the chain is long, and both the
   import of a library and the check of one recurse once per level of
   nesting, so this walk runs out of stack no sooner than they do. *)
let rec read_module env read mb =
  match mod_type mb, mod_expr mb with
  | MoreFunctor _, _ ->
    (* A functor: its fields are a functor body's, which no name of this
       walk reaches. *)
    keep_fields env read no_fields
  | NoFunctor _, Algebraic (MENoFunctor (MEident target)) ->
    (* [Module M := N] and [Module M : T := N]: N is the implementation. *)
    (match ModPath.Map.find_opt target (read_memo env) with
     | Some fields -> keep_fields env read fields
     | None ->
       match module_at env target with
       | None -> keep_fields env read no_fields
       | Some mb -> read_module env (target :: read) mb)
  | NoFunctor _, Algebraic _ ->
    (* An application of a functor: its fields are a functor body's too. *)
    keep_fields env read no_fields
  | NoFunctor _, Struct (_, struc) ->
    keep_fields env read (fields_of_structure struc)
  | NoFunctor struc, FullStruct ->
    (* [Module M. ... End M]: the type is the implementation. *)
    keep_fields env read (fields_of_structure struc)
  | NoFunctor _, Abstract ->
    (* [Declare Module M : T]: no implementation at all. *)
    keep_fields env read no_fields

(* A path's own root is the only module read from the environment. Under it,
   each module is the one its enclosing implementation declares, and a label
   that implementation does not declare is read no further: what the
   environment holds under such a name came from a type, which says nothing
   about what an implementation binds. *)
and module_at env mp =
  match mp with
  | MPfile _ | MPbound _ -> lookup_module env mp
  | MPdot (enclosing, lab) ->
    Id.Map.find_opt lab (fields_in_implementation env enclosing).modules

(* The path is walked from its root down, so that its own depth costs no
   stack. *)
and fields_in_implementation env mp =
  match ModPath.Map.find_opt mp (read_memo env) with
  | Some fields -> fields
  | None ->
    let rec split mp labs = match mp with
      | MPfile _ | MPbound _ -> mp, labs
      | MPdot (enclosing, lab) -> split enclosing (lab :: labs)
    in
    let root, labs = split mp [] in
    let descend (mp, fields) lab =
      let mp = MPdot (mp, lab) in
      match ModPath.Map.find_opt mp (read_memo env) with
      | Some fields -> mp, fields
      | None ->
        match Id.Map.find_opt lab fields.modules with
        | None -> mp, keep_fields env [mp] no_fields
        | Some mb -> mp, read_module env [mp] mb
    in
    let root_fields = match ModPath.Map.find_opt root (read_memo env) with
      | Some fields -> fields
      | None ->
        match lookup_module env root with
        | None -> keep_fields env [root] no_fields
        | Some mb -> read_module env [root] mb
    in
    snd (List.fold_left descend (root, root_fields) labs)

let defines_constant env kn =
  let mp, lab = KerName.repr (Constant.user kn) in
  match Id.Map.find_opt lab (fields_in_implementation env mp).constants with
  | Some has_body -> has_body
  | None -> false
