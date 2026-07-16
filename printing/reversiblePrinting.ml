(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type kind = Term | Type

type mode =
  | UpToUnification
  (** The reparsed term, with its holes, must unify with the original
      term (holes and universes get instantiated by unification). *)
  | UpToConversionModuloUniverses
  (** The reparsed term must elaborate on its own (no hole may need the
      original term to be resolved) to a term convertible with the
      original one, possibly enforcing new universe constraints on the
      universes introduced by the reparsing. *)
  | UpToConversion
  (** The reparsed term must elaborate on its own to a term convertible
      with the original one, with universe (in)equations valid in the
      current graph. *)

let mode_eq m1 m2 = match m1, m2 with
  | UpToUnification, UpToUnification
  | UpToConversionModuloUniverses, UpToConversionModuloUniverses
  | UpToConversion, UpToConversion -> true
  | (UpToUnification | UpToConversionModuloUniverses | UpToConversion), _ -> false

let current_mode : mode option ref = ref None

(* The three flags behave like a radio button: setting one unsets the
   others; unsetting the one currently set disables the check. *)
let declare_mode_option key mode =
  let open Goptions in
  declare_bool_option {
    optstage = Summary.Stage.Interp;
    optdepr  = None;
    optkey   = key;
    optread  = (fun () -> match !current_mode with
        | Some m -> mode_eq m mode
        | None -> false);
    optwrite = (fun b ->
        if b then current_mode := Some mode
        else match !current_mode with
          | Some m when mode_eq m mode -> current_mode := None
          | _ -> ());
  }

let () = declare_mode_option
    ["Printing";"Reversible";"Up";"To";"Unification"] UpToUnification
let () = declare_mode_option
    ["Printing";"Reversible";"Up";"To";"Conversion";"Modulo";"Universes"]
    UpToConversionModuloUniverses
let () = declare_mode_option
    ["Printing";"Reversible";"Up";"To";"Conversion"] UpToConversion

let pr_mode = function
  | UpToUnification -> Pp.str "unification"
  | UpToConversionModuloUniverses -> Pp.str "conversion modulo universes"
  | UpToConversion -> Pp.str "conversion"

let warn_not_reversible =
  CWarnings.create ~name:"reversible-printing"
    (fun mode ->
       Pp.(strbrk "The printed form of this term could not be re-parsed \
                   and re-elaborated to an equal term (up to " ++ pr_mode mode ++
           strbrk "), even with all printing options turned on."))

let lconstr_eoi = Procq.eoi_entry Procq.Constr.lconstr

(* Successively more explicit printing flags: coercions, implicit
   arguments, sorts, no notations, universes (first with, then without
   notations), parentheses, ending with the equivalent of
   [Printing All] plus [Printing Universes] and [Printing
   Parentheses]. Printing sorts is tried after implicit arguments and
   before unsetting notations; unsetting notations is tried before
   universes; neither is kept when escalating further (universes
   subsume sorts): configurations are ordered by explicitness, not
   included in each other. Only extern/detype-level flags and the
   [parentheses] flag may vary along the ladder: the rendering of the
   returned [constr_expr] must be fully determined by the returned
   flags (see [Ppconstr.of_printing_flags]). *)
let ladder flags =
  let open PrintingFlags in
  let e0 = flags.extern in
  let e1 = { e0 with Extern.coercions = true } in
  let e2 = { e1 with Extern.implicits = true; Extern.implicits_defensive = true } in
  let e3 = { e2 with Extern.notations = false } in
  let ds = { flags.detype with Detype.sorts = true } in
  let d4 = { flags.detype with Detype.universes = true } in
  let e5 = { e3 with Extern.parentheses = true } in
  let raw = make_raw flags in
  let raw = { detype = { raw.detype with Detype.universes = true };
              extern = { raw.extern with Extern.parentheses = true } } in
  [ flags;
    { flags with extern = e1 };
    { flags with extern = e2 };
    { detype = ds; extern = e2 };
    { flags with extern = e3 };
    { detype = d4; extern = e2 };
    { detype = d4; extern = e3 };
    { detype = d4; extern = e5 };
    raw ]

(* Reparsing a term can spuriously emit warnings (e.g. deprecation
   warnings for notations it reuses); silence them during the check. *)
let no_warnings f =
  let saved = CWarnings.get_flags () in
  CWarnings.set_flags "-all";
  try let v = f () in CWarnings.set_flags saved; v
  with e ->
    let e = Exninfo.capture e in
    CWarnings.set_flags saved;
    Exninfo.iraise e

let reparses ~mode ~kind ~flags env sigma t expr =
  try
    no_warnings begin fun () ->
      let ppflags = Ppconstr.of_printing_flags flags in
      let str = Pp.string_of_ppcmds (Ppconstr.pr_lconstr_expr ~flags:ppflags env sigma expr) in
      let expr = Procq.parse_string lconstr_eoi str in
      let expected_type = match kind with
        | Type -> Pretyping.IsType
        | Term -> Pretyping.WithoutTypeConstraint
      in
      let sigma', t' = Constrintern.interp_open_constr ~expected_type env sigma expr in
      let no_new_undefined () =
        Evar.Set.for_all (fun ev -> Evd.mem sigma ev)
          (Evarutil.undefined_evars_of_term sigma' t')
      in
      (* Conversion (and unification) of terms does not imply that they
         have convertible types (e.g. binder types of lambdas are not
         compared), so for terms we compare the types too. For [Type]
         kind we do not compare the (algebraic) sorts the types live
         in, as elaboration is anyway allowed to pick different such
         sorts for the very same expression. *)
      let pairs = match kind with
        | Type -> [t', t]
        | Term ->
          let ty' = Retyping.get_type_of env sigma' t' in
          let ty = Retyping.get_type_of env sigma' t in
          [ty', ty; t', t]
      in
      match mode with
      | UpToUnification ->
        let sigma' = List.fold_left (fun sigma' (t', t) ->
            Evarconv.unify_delay env sigma' t' t) sigma' pairs in
        let (_ : Evd.evar_map) = Evarconv.solve_unif_constraints_with_heuristics env sigma' in
        true
      | UpToConversionModuloUniverses ->
        no_new_undefined () &&
        (let rec conv sigma' = function
           | [] -> true
           | (t', t) :: pairs ->
             match Reductionops.infer_conv ~pb:Conversion.CONV env sigma' t' t with
             | Some sigma' -> conv sigma' pairs
             | None -> false
         in
         conv sigma' pairs)
      | UpToConversion ->
        no_new_undefined () &&
        List.for_all (fun (t', t) -> Reductionops.is_conv env sigma' t' t) pairs
    end
  with e when CErrors.noncritical e -> false

(* Printing terms while checking reversibility (e.g. from the
   elaboration of the reparsed term) must not recursively trigger the
   check. *)
let in_check = ref false

let checked_extern ~flags ~extern ~kind env sigma t =
  match !current_mode with
  | None -> flags, extern ~flags
  | Some _ when !in_check -> flags, extern ~flags
  | Some mode ->
    in_check := true;
    try
      let rec aux = function
        | [] -> assert false
        | [flags] ->
          let expr = extern ~flags in
          if not (reparses ~mode ~kind ~flags env sigma t expr) then
            warn_not_reversible mode;
          (flags, expr)
        | flags :: rest ->
          let expr = extern ~flags in
          if reparses ~mode ~kind ~flags env sigma t expr then (flags, expr)
          else aux rest
      in
      let v = aux (ladder flags) in
      in_check := false;
      v
    with e ->
      let e = Exninfo.capture e in
      in_check := false;
      Exninfo.iraise e
