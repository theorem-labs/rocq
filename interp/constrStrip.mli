(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {5 Location stripping of concrete syntax and notations}

    Each function returns a copy of its argument in which every source
    location is replaced by the fixed value of {!LocStrip}; nothing else
    changes. Used only to compute the location-free interface key of a
    library.

    A raw generic argument ([CGenarg]) has no registered stripper: stripping
    a [constr_expr] that contains one raises [LocStrip.Unknown]. *)

open Names
open Constrexpr

val qualid : Libnames.qualid -> Libnames.qualid
val lident : lident -> lident
val lname : lname -> lname
val or_by_notation : ('a -> 'a) -> 'a or_by_notation -> 'a or_by_notation

(** Universes and sorts *)

val sort_name_expr : sort_name_expr -> sort_name_expr
val univ_level_expr : univ_level_expr -> univ_level_expr
val qvar_expr : qvar_expr -> qvar_expr
val quality_expr : quality_expr -> quality_expr
val relevance_expr : relevance_expr -> relevance_expr
val relevance_info_expr : relevance_info_expr -> relevance_info_expr
val sort_expr : sort_expr -> sort_expr
val instance_expr : instance_expr -> instance_expr
val univ_constraint_expr : univ_constraint_expr -> univ_constraint_expr
val elim_constraint_expr : elim_constraint_expr -> elim_constraint_expr
val sort_constraint_expr : sort_constraint_expr -> sort_constraint_expr
val universe_decl_expr : universe_decl_expr -> universe_decl_expr
val lident_with_variance : lident_with_variance -> lident_with_variance
val cumul_univ_decl_expr : cumul_univ_decl_expr -> cumul_univ_decl_expr
val ident_decl : ident_decl -> ident_decl
val cumul_ident_decl : cumul_ident_decl -> cumul_ident_decl
val name_decl : name_decl -> name_decl

(** Terms *)

val constr_expr : constr_expr -> constr_expr
val cases_pattern_expr : cases_pattern_expr -> cases_pattern_expr
val kinded_cases_pattern_expr : kinded_cases_pattern_expr -> kinded_cases_pattern_expr
val cases_pattern_notation_substitution :
  cases_pattern_notation_substitution -> cases_pattern_notation_substitution
val constr_notation_substitution : constr_notation_substitution -> constr_notation_substitution
val local_binder_expr : local_binder_expr -> local_binder_expr
val case_expr : case_expr -> case_expr
val branch_expr : branch_expr -> branch_expr
val fix_expr : fix_expr -> fix_expr
val cofix_expr : cofix_expr -> cofix_expr
val fixpoint_order_expr : fixpoint_order_expr -> fixpoint_order_expr
val explicitation : explicitation CAst.t -> explicitation CAst.t

(** Modules *)

val with_declaration_ast : with_declaration_ast -> with_declaration_ast
val module_ast : module_ast -> module_ast

(** Globalized terms paired with their source *)

val glob_constr_and_expr : Genintern.glob_constr_and_expr -> Genintern.glob_constr_and_expr
val glob_constr_pattern_and_expr :
  Genintern.glob_constr_pattern_and_expr -> Genintern.glob_constr_pattern_and_expr

(** Notations *)

val notation_constr : Notation_term.notation_constr -> Notation_term.notation_constr
val interpretation : Notation_term.interpretation -> Notation_term.interpretation
