(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Names
open Libnames
open Libobject
open Lib
open Notationextern

type abbreviation = {
  abbrev_local : Libobject.locality;
  abbrev_pattern : Notation_term.interpretation;
  abbrev_onlyparsing : bool;
  abbrev_user_warns : Globnames.extended_global_reference UserWarn.with_qf option;
  abbrev_activated : bool; (* Not really necessary in practice *)
  abbrev_src : Loc.t option;
}

type data = full_path * abbreviation

let interp (_, a) = a.abbrev_pattern
let full_path (fp, _) = fp
let enabled (_, a) = a.abbrev_activated
let only_parsing (_, a) = a.abbrev_onlyparsing

let abbrev_table =
  Summary.ref (KerName.Map.empty : data KerName.Map.t) ~name:"ABBREVIATIONS"

let add kn fpa =
  abbrev_table := KerName.Map.add kn fpa !abbrev_table

let fold f acc =
  KerName.Map.fold f !abbrev_table acc

let find_opt k =
  KerName.Map.find_opt k !abbrev_table

let toggle_aux ~on ~use k (sp, data) =
  if data.abbrev_activated != on then begin
    abbrev_table := KerName.Map.add k (sp, {data with abbrev_activated = on}) !abbrev_table;
    match use with
    | OnlyPrinting -> ()
    | (OnlyParsing | ParsingAndPrinting) when on ->
        Nametab.push_abbreviation ?user_warns:data.abbrev_user_warns (Nametab.Until 1) sp k;
        Nametab.push_abbreviation (Nametab.Exactly 1) sp k
    | OnlyParsing | ParsingAndPrinting ->
        Nametab.remove_abbreviation sp k
  end

let toggle ~on ~use k =
  toggle_aux ~on ~use k (KerName.Map.find k !abbrev_table)

let toggle_if ~on ~use filter =
  fold (fun k ((_, a) as abbr) _ ->
    if a.abbrev_activated != on && filter k abbr then
      toggle_aux ~on ~use k abbr
  ) ()

let is_alias_of_already_visible_name sp = function
  | _,Notation_term.NRef (ref,None) ->
      let (dir,id) = repr_qualid (Nametab.shortest_qualid_of_global ~force_short:true Id.Set.empty ref) in
      DirPath.is_empty dir && Id.equal id (basename sp)
  | _ ->
      false

let load_abbreviation i ((sp,kn),abbrev) =
  if Nametab.exists_cci sp then
    user_err
      (Id.print (basename sp) ++ str " already exists.");
  add kn (sp, abbrev);
  Nametab.push_abbreviation ?user_warns:abbrev.abbrev_user_warns (Nametab.Until i) sp kn;
  abbrev.abbrev_src |> Option.iter (fun loc -> Nametab.set_cci_src_loc (Abbrev kn) loc);
  let pat = abbrev.abbrev_pattern in
  let () = if not abbrev.abbrev_onlyparsing &&
              abbrev.abbrev_local <> Export &&
              not (Int.equal i 1 && is_alias_of_already_visible_name sp pat) then
      Notationextern.declare_uninterpretation (Global.env ()) (AbbrevRule kn) pat
  in
  ()

let open_abbreviation i ((sp,kn),abbrev) =
  let pat = abbrev.abbrev_pattern in
  if not (Int.equal i 1 && is_alias_of_already_visible_name sp pat) then begin
    Nametab.push_abbreviation (Nametab.Exactly i) sp kn;
    if not abbrev.abbrev_onlyparsing &&
       Int.equal i 1 &&
       abbrev.abbrev_local <> SuperGlobal then
      Notationextern.declare_uninterpretation (Global.env ()) (AbbrevRule kn) pat
  end

let import i sp kn =
  let _,abbrev = KerName.Map.get kn !abbrev_table in
  open_abbreviation i ((sp,kn),abbrev)

let cache_abbreviation d =
  load_abbreviation 1 d;
  open_abbreviation 1 d

let subst_abbreviation (subst,abbrev) =
  let abbrev_pattern = Notation_ops.subst_interpretation subst abbrev.abbrev_pattern in
  { abbrev with abbrev_pattern }

let classify_abbreviation abbrev =
  if abbrev.abbrev_local = Local then Dispose else Substitute

(** binary-equivalence-taiga#841 round 7 (ab1): [declare_named_object_full]
    rather than [declare_named_object], so [cutoff_abbrev_entry] below can
    [Dyn.Easy.prj] against this object's own tag and read back the
    abbreviation's own [Id.t] and semantic content directly -- same shape
    as [Impargs.cutoff_implicits_targets]/
    [Notation.cutoff_arguments_scope_target]. Produces the EXACT SAME
    [obj] value [declare_named_object] would have (confirmed from
    [Libobject]'s own implementation: [declare_named_object odecl] is
    exactly [let tag = declare_named_object_full odecl in fun id v ->
    Dyn.Dyn (tag, (id, v))], and [Dyn.Easy.inj x tag = Dyn.Dyn (tag, x)]),
    so this is a representation-only change with no effect on caching,
    loading, substitution or discharge. *)
let objAbbreviation : (Id.t * abbreviation) Libobject.Dyn.tag =
  declare_named_object_full {(default_object "ABBREVIATION") with
    cache_function = cache_abbreviation;
    load_function = load_abbreviation;
    open_function = filtered_open open_abbreviation;
    subst_function = subst_abbreviation;
    classify_function = classify_abbreviation }

let inAbbreviation (id : Id.t) (abbrev : abbreviation) : obj =
  Libobject.Dyn.Easy.inj (id, abbrev) objAbbreviation

(** binary-equivalence-taiga#841 round 7 (ab1): an abbreviation
    (`Notation foo := bar`) is a short NAME, resolvable and shadowable
    exactly like a `Definition`, but it is not an [SFBconst]/[SFBmind]
    and so is invisible to the kernel's own [Safe_typing.iface_table] --
    a dependency that later adds a REAL declaration colliding with an
    abbreviation's name was invisible to the G7 shadow check, since
    nothing recorded the abbreviation's name as "already in use" in the
    first place. Fix: hand [(Id.t, Digest.t)] entries for every
    exported abbreviation to [Safe_typing.export]'s
    [extra_closure_names] parameter (see
    [Declaremods.G1Partition.abbrev_iface_entries]), which folds them
    into the SAME per-library table as an ordinary top-level
    declaration, so either side of a collision is caught regardless of
    which one is the abbreviation. The digest covers exactly what a
    dependent can observe by using the name: its expansion
    ([abbrev_pattern]), whether it is parsing-only ([abbrev_onlyparsing],
    affecting whether the name can be used in a term at all) and whether
    it is active ([abbrev_activated]) -- deliberately excluding
    [abbrev_local] (already filtered: [classify_abbreviation] disposes
    of [Local] abbreviations before export, so only non-local ones ever
    reach this walk), [abbrev_src] (a source location) and
    [abbrev_user_warns] (a deprecation message), all presentation-only. *)
let cutoff_abbrev_entry (obj : obj) : (Id.t * Digest.t) option =
  match Libobject.Dyn.Easy.prj obj objAbbreviation with
  | Some (id, abbrev) ->
    let d = Csha256.digest (Marshal.to_string
      (abbrev.abbrev_pattern, abbrev.abbrev_onlyparsing, abbrev.abbrev_activated) []) in
    Some (id, d)
  | None -> None

let declare ~local user_warns id ~onlyparsing pat =
  let abbrev = {
    abbrev_local = local;
    abbrev_pattern = pat;
    abbrev_onlyparsing = onlyparsing;
    abbrev_user_warns = user_warns;
    abbrev_activated = true;
    abbrev_src = Loc.get_current_command_loc();
    }
  in
  add_leaf (inAbbreviation id abbrev)

(* Remark: do not check for activation (if not activated, it is already not supposed to be located) *)
let find_interp kn =
  let _,abbrev = KerName.Map.find kn !abbrev_table in
  abbrev.abbrev_pattern
