(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Typed location stripping of globalized Ltac1 values (see [LocStrip]).
    Each function returns a copy in which every location is replaced and
    nothing else differs. Linking this module registers the [Genstrip]
    strippers of the arguments of [Tacarg]. *)

open Tacexpr
open Tactypes

val strip_tactic : glob_tactic_expr -> glob_tactic_expr
val glob_tactic_expr : glob_tactic_expr -> glob_tactic_expr
(** Same as [strip_tactic]. *)

val strip_tactic_arg : glob_tactic_arg -> glob_tactic_arg

val lident : Names.lident -> Names.lident
val or_var : ('a -> 'a) -> 'a Locus.or_var -> 'a Locus.or_var
val occurrences_expr : Locus.occurrences_expr -> Locus.occurrences_expr
val clause_expr : g_nam Locus.clause_expr -> g_nam Locus.clause_expr
val quantified_hypothesis : quantified_hypothesis -> quantified_hypothesis
val bindings : g_trm bindings -> g_trm bindings
val with_bindings : g_trm with_bindings -> g_trm with_bindings
val with_bindings_arg : g_trm with_bindings_arg -> g_trm with_bindings_arg
val intro_pattern : g_trm intro_pattern_expr CAst.t -> g_trm intro_pattern_expr CAst.t
val or_and_intro_pattern :
  g_trm or_and_intro_pattern_expr CAst.t -> g_trm or_and_intro_pattern_expr CAst.t
val destruction_arg :
  g_trm with_bindings Tactics.destruction_arg -> g_trm with_bindings Tactics.destruction_arg
val red_expr : Redexpr.glob_red_expr -> Redexpr.glob_red_expr
