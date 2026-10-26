(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {5 Location stripping of globalized terms}

    Each function returns a copy of its argument in which every source
    location is replaced by the fixed value of {!LocStrip}; nothing else
    changes. Generic arguments are stripped through {!Genstrip}. Used only to
    compute the location-free interface key of a library. *)

open Glob_term

val glob_constr : 'a glob_constr_g -> 'a glob_constr_g
val cases_pattern : 'a cases_pattern_g -> 'a cases_pattern_g
val glob_sort : glob_sort -> glob_sort
val glob_level : glob_level -> glob_level
val glob_qvar : glob_qvar -> glob_qvar
val glob_relevance : glob_relevance -> glob_relevance
val glob_quality : glob_quality -> glob_quality
val glob_sort_name : glob_sort_name -> glob_sort_name
val glob_instance : glob_instance -> glob_instance
val glob_constraint : glob_constraint -> glob_constraint
val extended_glob_local_binder : 'a extended_glob_local_binder_g -> 'a extended_glob_local_binder_g
val glob_decl : 'a glob_decl_g -> 'a glob_decl_g
val predicate_pattern : 'a predicate_pattern_g -> 'a predicate_pattern_g
val tomatch_tuple : 'a tomatch_tuple_g -> 'a tomatch_tuple_g
val cases_clause : 'a cases_clause_g -> 'a cases_clause_g
val disjunctive_cases_clause : 'a disjunctive_cases_clause_g -> 'a disjunctive_cases_clause_g

val uninstantiated_pattern : Pattern.uninstantiated_pattern -> Pattern.uninstantiated_pattern
(** Only [PExtra] can hold a location (a generic argument). *)

(** {6 Locus} *)

val or_var : ('a -> 'b) -> 'a Locus.or_var -> 'b Locus.or_var
val occurrences_gen : ('a -> 'b) -> 'a Locus.occurrences_gen -> 'b Locus.occurrences_gen
val occurrences_expr : Locus.occurrences_expr -> Locus.occurrences_expr
val hyp_location_expr : ('a -> 'b) -> 'a Locus.hyp_location_expr -> 'b Locus.hyp_location_expr
val clause_expr : ('a -> 'b) -> 'a Locus.clause_expr -> 'b Locus.clause_expr
