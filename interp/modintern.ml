(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Mod_declarations
open Libnames
open Constrexpr
open Constrintern

type module_internalization_error =
  | NotAModuleNorModtype of qualid
  | NotAModuleType of qualid
  | NotAModule of qualid
  | IncorrectWithInModule
  | IncorrectModuleApplication

exception ModuleInternalizationError of module_internalization_error

type module_kind = Module | ModType | ModAny

type module_struct_expr = (universe_decl_expr option * constr_expr) Declarations.module_alg_expr

let error_not_a_module_loc ~info kind loc qid =
  let e = match kind with
    | Module -> NotAModule qid
    | ModType -> NotAModuleType qid
    | ModAny -> NotAModuleNorModtype qid
  in
  let info = Option.cata (Loc.add_loc info) info loc in
  Exninfo.iraise (ModuleInternalizationError e,info)

let error_incorrect_with_in_module loc =
  Loc.raise ?loc (ModuleInternalizationError IncorrectWithInModule)

let error_application_to_module_type loc =
  Loc.raise ?loc (ModuleInternalizationError IncorrectModuleApplication)

(** Searching for a module name in the Nametab.

    According to the input module kind, modules or module types
    or both are searched. The returned kind is never ModAny, and
    it is equal to the input kind when this one isn't ModAny. *)

let lookup_module_or_modtype kind qid =
  let loc = qid.CAst.loc in
  try
    if kind == ModType then raise Not_found;
    let mp = Nametab.locate_module qid in
    Dumpglob.dump_modref ?loc mp "mod"; (mp,Module)
  with Not_found ->
    try
      if kind == Module then raise Not_found;
      let mp = Nametab.locate_modtype qid in
      Dumpglob.dump_modref ?loc mp "modtype"; (mp,ModType)
    with Not_found as exn ->
      let _, info = Exninfo.capture exn in
      error_not_a_module_loc ~info kind loc qid

let lookup_module lqid = fst (lookup_module_or_modtype Module lqid)

let lookup_polymorphism env base kind fqid =
  let m = match kind with
    | Module -> mod_type (Environ.lookup_module base env)
    | ModType -> mod_type (Environ.lookup_modtype base env)
    | ModAny -> assert false
  in
  let rec defunctor = function
    | NoFunctor m -> m
    | MoreFunctor (_,_,m) -> defunctor m
  in
  let rec aux m fqid =
    let open Names in
    match fqid with
    | [] -> assert false
    | [id] ->
      let test (lab,obj) =
        match Id.equal lab id, obj with
        | false, _ | _, (SFBrules _ | SFBmodule _ | SFBmodtype _) -> None
        | true, SFBmind mind -> Some (Declareops.inductive_is_polymorphic mind)
        | true, SFBconst const -> Some (Declareops.constant_is_polymorphic const)
      in
      (match CList.find_map test m with Some v -> v | None -> false (* error later *))
    | id::rem ->
      let next = function
        | MoreFunctor _ -> false (* error later *)
        | NoFunctor body -> aux body rem
      in
      let test (lab,obj) =
        match Id.equal lab id, obj with
        | false, _ | _, (SFBrules _ | SFBconst _ | SFBmind _) -> None
        | true, SFBmodule body -> Some (next @@ mod_type body)
        | true, SFBmodtype body ->  (* XXX is this valid? If not error later *)
          Some (next @@ mod_type body)
      in
      (match CList.find_map test m with Some v -> v | None -> false (* error later *))
  in
  aux (defunctor m) fqid

let intern_with_decl = function
  | CWith_Module ({CAst.v=fqid},qid) ->
    WithMod (fqid,lookup_module qid)
  | CWith_Definition ({CAst.v=fqid},udecl,c) ->
    WithDef (fqid,(udecl,c))

let loc_of_module l = l.CAst.loc

(** binary-equivalence-taiga#841 round 23: every module path a module
    expression in this file names. A module expression is the only way a
    file copies another library's structure into its own compiled form:
    [Module K := A], [Include A], [Module K. Include A. End K.], a functor
    application [F X], a [with Module] constraint, and the signature in
    [Module M : T]. All of them reach the kernel through
    [interp_module_ast] below, which is why the record is taken here, at
    the one funnel, rather than recovered afterwards from the stored
    objects: [get_module_sobjs]'s [MEwith] case expands the copied objects
    inline ([Objs], not [Ref]), losing the name of the library they came
    from, and a functor argument appears only inside a substitution.

    [Declaremods.end_library] turns these paths into the library's
    structural dependency list, and clears the record for the next library
    this process compiles. Loading a [.vo] never interprets a module
    expression, so nothing accumulates here while a library is required.

    Deliberately NOT a [Summary.ref]: the summary is saved and restored
    around a module declaration, so a target named INSIDE a module (a
    nested [Include A], and the body of [Module K := A] itself) would be
    rolled back when the module closes, which is exactly the shape of the
    round-22 hole. A plain reference can only ever over-record -- an
    expression whose command later failed or was undone stays in the list
    and costs a refusal, never a reuse. *)
let structural_targets_ref = ref Names.ModPath.Set.empty

let note_structural_target mp =
  structural_targets_ref := Names.ModPath.Set.add mp !structural_targets_ref

let rec note_module_expr : 'a. 'a Declarations.module_alg_expr -> unit = function
  | MEident mp -> note_structural_target mp
  | MEapply (me, mp) -> note_module_expr me; note_structural_target mp
  | MEwith (me, WithMod (_, mp)) -> note_module_expr me; note_structural_target mp
  | MEwith (me, WithDef _) -> note_module_expr me

let structural_targets () = Names.ModPath.Set.elements !structural_targets_ref

let clear_structural_targets () = structural_targets_ref := Names.ModPath.Set.empty

(* Invariant : the returned kind is never ModAny, and it is
   equal to the input kind when this one isn't ModAny. *)

let rec intern_module_ast kind m = match m with
  | {CAst.loc;v=CMident qid} ->
      let (mp,kind) = lookup_module_or_modtype kind qid in
      (MEident mp, mp, kind)
  | {CAst.loc;v=CMapply (me1,me2)} ->
      let me1', base, kind1 = intern_module_ast kind me1 in
      let mp2, kind2 = lookup_module_or_modtype ModAny me2 in
      if kind2 == ModType then
        error_application_to_module_type (loc_of_module me2);
      (MEapply (me1',mp2), base, kind1)
  | {CAst.loc;v=CMwith (me,decl)} ->
      let me,base,kind = intern_module_ast kind me in
      if kind == Module then error_incorrect_with_in_module m.CAst.loc;
      let decl = intern_with_decl decl in
      (MEwith(me,decl), base, kind)

let interp_with_decl env base kind = function
  | WithMod (fqid,mp) -> WithMod (fqid,mp), Univ.ContextSet.empty
  | WithDef(fqid,(udecl,c)) ->
    let sigma, udecl = interp_univ_decl_opt env udecl in
    let c, ectx = interp_constr env sigma c in
    let poly = lookup_polymorphism env base kind fqid in
    let poly =
      PolyFlags.of_univ_poly poly (* MS: FIXME: no sortpoly/cumulative support *)
    in
    begin match fst (UState.check_univ_decl ~poly ectx udecl) with
      | UState.Polymorphic_entry ctx ->
        let inst, ctx = UVars.abstract_universes ctx in
        let c = EConstr.Vars.subst_univs_level_constr (UVars.make_instance_subst inst) c in
        let c = EConstr.to_constr sigma c in
        WithDef (fqid,(c, Some ctx)), Univ.ContextSet.empty
      | UState.Monomorphic_entry ctx ->
        let c = EConstr.to_constr sigma c in
        WithDef (fqid,(c, None)), ctx
    end

let rec interp_module_ast env kind base m cst = match m with
| MEident mp ->
  MEident mp, cst
| MEapply (me,mp) ->
  let me', cst = interp_module_ast env kind base me cst in
  MEapply(me',mp), cst
| MEwith(me,decl) ->
  let me, cst = interp_module_ast env kind base me cst in
  let decl, cst' = interp_with_decl env base kind decl in
  let cst = Univ.ContextSet.union cst cst' in
  MEwith(me,decl), cst

let interp_module_ast env kind base m =
  (* Record before interpreting: the paths are the same either way, and a
     failure here never reaches [end_library]. *)
  note_module_expr m;
  interp_module_ast env kind base m Univ.ContextSet.empty
