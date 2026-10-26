(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Typed location stripping of globalized Ltac1 tactics, for the
    location-free interface key of a library (see [Libobject.interface_key]).
    Same traversal as [Tacsubst], but every location is reached. *)

open Locus
open Tactypes
open Tacexpr

let id x = x

let lident (x : Names.lident) = LocStrip.cast id x
let lname (x : Names.lname) = LocStrip.cast id x

let or_var f = function
  | ArgArg x -> ArgArg (f x)
  | ArgVar v -> ArgVar (lident v)

let g_trm = ConstrStrip.glob_constr_and_expr
let g_pat = ConstrStrip.glob_constr_pattern_and_expr

let occurrences_gen f = function
  | AllOccurrences -> AllOccurrences
  | AtLeastOneOccurrence -> AtLeastOneOccurrence
  | AllOccurrencesBut l -> AllOccurrencesBut (List.map f l)
  | NoOccurrences -> NoOccurrences
  | OnlyOccurrences l -> OnlyOccurrences (List.map f l)

let occurrences_expr (o : occurrences_expr) = occurrences_gen (or_var id) o

let clause_expr (cl : g_nam clause_expr) =
  let hyp ((occs, h), flag) = ((occurrences_expr occs, lident h), flag) in
  { onhyps = Option.map (List.map hyp) cl.onhyps;
    concl_occs = occurrences_expr cl.concl_occs }

let quantified_hypothesis = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id -> NamedHyp (lident id)

let bindings (b : g_trm bindings) = match b with
  | ImplicitBindings l -> ImplicitBindings (List.map g_trm l)
  | ExplicitBindings l ->
    ExplicitBindings
      (List.map (LocStrip.cast (fun (h, c) -> (quantified_hypothesis h, g_trm c))) l)
  | NoBindings -> NoBindings

let with_bindings ((c, bl) : g_trm with_bindings) = (g_trm c, bindings bl)

let with_bindings_arg ((clear, c) : g_trm with_bindings_arg) = (clear, with_bindings c)

let intro_pattern_naming (n : Namegen.intro_pattern_naming_expr CAst.t) =
  (* [intro_pattern_naming_expr] holds identifiers only. *)
  LocStrip.cast id n

let rec intro_pattern (p : g_trm intro_pattern_expr CAst.t) =
  LocStrip.cast intro_pattern_expr p

and intro_pattern_expr = function
  | IntroForthcoming b -> IntroForthcoming b
  | IntroNaming n -> IntroNaming n
  | IntroAction a -> IntroAction (intro_pattern_action a)

and intro_pattern_action = function
  | IntroWildcard -> IntroWildcard
  | IntroOrAndPattern p -> IntroOrAndPattern (or_and_intro_pattern_expr p)
  | IntroInjection l -> IntroInjection (List.map intro_pattern l)
  | IntroApplyOn (c, p) -> IntroApplyOn (LocStrip.cast g_trm c, intro_pattern p)
  | IntroRewrite b -> IntroRewrite b

and or_and_intro_pattern_expr = function
  | IntroOrPattern ll -> IntroOrPattern (List.map (List.map intro_pattern) ll)
  | IntroAndPattern l -> IntroAndPattern (List.map intro_pattern l)

let or_and_intro_pattern (p : g_trm or_and_intro_pattern_expr CAst.t) =
  LocStrip.cast or_and_intro_pattern_expr p

let destruction_arg ((clear, c) : g_trm with_bindings Tactics.destruction_arg) =
  let c = match c with
    | Tactics.ElimOnConstr c -> Tactics.ElimOnConstr (with_bindings c)
    | Tactics.ElimOnIdent id -> Tactics.ElimOnIdent (lident id)
    | Tactics.ElimOnAnonHyp n -> Tactics.ElimOnAnonHyp n
  in
  (clear, c)

let red_expr (r : Redexpr.glob_red_expr) = Redexpr.strip_glob_red_expr r

let g_cst (c : g_cst) = or_var (fun (e, n) -> (e, Option.map lident n)) c

let g_ref (r : g_ref) = or_var (LocStrip.located id) r

let message_token = function
  | MsgString s -> MsgString s
  | MsgInt n -> MsgInt n
  | MsgIdent id -> MsgIdent (lident id)

let may_eval = function
  | ConstrTerm c -> ConstrTerm (g_trm c)
  | ConstrEval (r, c) -> ConstrEval (red_expr r, g_trm c)
  | ConstrContext (id, c) -> ConstrContext (lident id, g_trm c)
  | ConstrTypeOf c -> ConstrTypeOf (g_trm c)

let match_pattern = function
  | Term p -> Term (g_pat p)
  | Subterm (ido, p) -> Subterm (ido, g_pat p)

let match_context_hyps = function
  | Hyp (na, mp) -> Hyp (lname na, match_pattern mp)
  | Def (na, mv, mp) -> Def (lname na, match_pattern mv, match_pattern mp)

let inversion_strength = function
  | NonDepInversion (k, ids, p) ->
    NonDepInversion (k, List.map lident ids, Option.map (or_var or_and_intro_pattern) p)
  | DepInversion (k, c, p) ->
    DepInversion (k, Option.map g_trm c, Option.map (or_var or_and_intro_pattern) p)
  | InversionUsing (c, ids) -> InversionUsing (g_trm c, List.map lident ids)

let induction_clause (c, (eqn, as_), cl) =
  (destruction_arg c,
   (Option.map intro_pattern_naming eqn, Option.map (or_var or_and_intro_pattern) as_),
   Option.map clause_expr cl)

let rec atomic (t : glob_atomic_tactic_expr) : glob_atomic_tactic_expr = match t with
  | TacIntroPattern (ev, l) -> TacIntroPattern (ev, List.map intro_pattern l)
  | TacApply (a, ev, cb, cl) ->
    TacApply (a, ev, List.map with_bindings_arg cb,
              List.map (fun (na, p) -> (lident na, Option.map intro_pattern p)) cl)
  | TacElim (ev, cb, cbo) ->
    TacElim (ev, with_bindings_arg cb, Option.map with_bindings cbo)
  | TacCase (ev, cb) -> TacCase (ev, with_bindings_arg cb)
  | TacMutualFix (id, n, l) ->
    TacMutualFix (id, n, List.map (fun (id, n, c) -> (id, n, g_trm c)) l)
  | TacMutualCofix (id, l) ->
    TacMutualCofix (id, List.map (fun (id, c) -> (id, g_trm c)) l)
  | TacAssert (ev, b, otac, p, c) ->
    TacAssert (ev, b, Option.map (Option.map strip_tactic) otac,
               Option.map intro_pattern p, g_trm c)
  | TacGeneralize cl ->
    TacGeneralize
      (List.map (fun ((occs, c), na) -> ((occurrences_gen (or_var id) occs, g_trm c), na)) cl)
  | TacLetTac (ev, na, c, cl, b, eqpat) ->
    TacLetTac (ev, na, g_trm c, clause_expr cl, b, Option.map intro_pattern_naming eqpat)
  | TacInductionDestruct (isrec, ev, (l, el)) ->
    TacInductionDestruct (isrec, ev, (List.map induction_clause l, Option.map with_bindings el))
  | TacReduce (r, cl) -> TacReduce (red_expr r, clause_expr cl)
  | TacChange (check, op, c, cl) ->
    TacChange (check, Option.map g_trm op, g_trm c, clause_expr cl)
  | TacRewrite (ev, l, cl, by) ->
    TacRewrite (ev, List.map (fun (b, m, c) -> (b, m, with_bindings_arg c)) l,
                clause_expr cl, Option.map strip_tactic by)
  | TacInversion (s, h) -> TacInversion (inversion_strength s, quantified_hypothesis h)

and strip_tactic (t : glob_tactic_expr) : glob_tactic_expr = LocStrip.cast tactic_r t

and tactic_r = function
  | TacAtom t -> TacAtom (atomic t)
  | TacThen (t1, t2) -> TacThen (strip_tactic t1, strip_tactic t2)
  | TacDispatch tl -> TacDispatch (List.map strip_tactic tl)
  | TacExtendTac (tf, t, tl) ->
    TacExtendTac (Array.map strip_tactic tf, strip_tactic t, Array.map strip_tactic tl)
  | TacThens (t, tl) -> TacThens (strip_tactic t, List.map strip_tactic tl)
  | TacThens3parts (t1, tf, t2, tl) ->
    TacThens3parts (strip_tactic t1, Array.map strip_tactic tf,
                    strip_tactic t2, Array.map strip_tactic tl)
  | TacFirst l -> TacFirst (List.map strip_tactic l)
  | TacSolve l -> TacSolve (List.map strip_tactic l)
  | TacTry t -> TacTry (strip_tactic t)
  | TacOr (t1, t2) -> TacOr (strip_tactic t1, strip_tactic t2)
  | TacOnce t -> TacOnce (strip_tactic t)
  | TacExactlyOnce t -> TacExactlyOnce (strip_tactic t)
  | TacIfThenCatch (t, tt, te) ->
    TacIfThenCatch (strip_tactic t, strip_tactic tt, strip_tactic te)
  | TacOrelse (t1, t2) -> TacOrelse (strip_tactic t1, strip_tactic t2)
  | TacDo (n, t) -> TacDo (or_var id n, strip_tactic t)
  | TacTimeout (n, t) -> TacTimeout (or_var id n, strip_tactic t)
  | TacTime (s, t) -> TacTime (s, strip_tactic t)
  | TacRepeat t -> TacRepeat (strip_tactic t)
  | TacProgress t -> TacProgress (strip_tactic t)
  | TacAbstract (t, ido) -> TacAbstract (strip_tactic t, ido)
  | TacId l -> TacId (List.map message_token l)
  | TacFail (g, n, l) -> TacFail (g, or_var id n, List.map message_token l)
  | TacLetIn (r, l, t) ->
    TacLetIn (r, List.map (fun (na, a) -> (lname na, strip_tactic_arg a)) l, strip_tactic t)
  | TacMatch (lz, t, rules) -> TacMatch (lz, strip_tactic t, List.map match_rule rules)
  | TacMatchGoal (lz, lr, rules) -> TacMatchGoal (lz, lr, List.map match_rule rules)
  | TacFun (vars, body) -> TacFun (vars, strip_tactic body)
  | TacArg a -> TacArg (strip_tactic_arg a)
  | TacSelect (s, t) -> TacSelect (s, strip_tactic t)
  | TacML (e, l) -> TacML (e, List.map strip_tactic_arg l)
  | TacAlias (kn, l) -> TacAlias (kn, List.map strip_tactic_arg l)

and strip_tactic_arg (a : glob_tactic_arg) : glob_tactic_arg = match a with
  | TacGeneric (q, arg) -> TacGeneric (q, Genstrip.generic_strip arg)
  | ConstrMayEval c -> ConstrMayEval (may_eval c)
  | Reference r -> Reference (g_ref r)
  | TacCall c ->
    TacCall (LocStrip.cast (fun (f, l) -> (g_ref f, List.map strip_tactic_arg l)) c)
  | TacFreshId l -> TacFreshId (List.map (or_var id) l)
  | Tacexp t -> Tacexp (strip_tactic t)
  | TacPretype c -> TacPretype (g_trm c)
  | TacNumgoals -> TacNumgoals

and match_rule = function
  | Pat (hyps, mp, t) -> Pat (List.map match_context_hyps hyps, match_pattern mp, strip_tactic t)
  | All t -> All (strip_tactic t)

let glob_tactic_expr = strip_tactic

(** Registering *)

let () =
  let open Tacarg in
  Genstrip.register_strip0 wit_intropattern intro_pattern [@warning "-3"];
  Genstrip.register_strip0 wit_simple_intropattern intro_pattern;
  Genstrip.register_strip0 wit_quant_hyp quantified_hypothesis;
  Genstrip.register_strip0 wit_constr_with_bindings with_bindings;
  Genstrip.register_strip0 wit_open_constr_with_bindings with_bindings;
  Genstrip.register_strip0 wit_bindings bindings;
  Genstrip.register_strip0 wit_tactic strip_tactic;
  Genstrip.register_strip0 wit_ltac_in_term (fun (used, t) -> (used, strip_tactic t));
  Genstrip.register_strip0 wit_ltac strip_tactic;
  Genstrip.register_strip0 wit_destruction_arg destruction_arg
