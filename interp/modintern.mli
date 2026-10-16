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
open Environ
open Entries
open Constrexpr
open Libnames

(** Module internalization errors *)

type module_internalization_error =
  | NotAModuleNorModtype of qualid
  | NotAModuleType of qualid
  | NotAModule of qualid
  | IncorrectWithInModule
  | IncorrectModuleApplication

exception ModuleInternalizationError of module_internalization_error

(** Module expressions and module types are interpreted relatively to
   possible functor or functor signature arguments. When the input kind
   is ModAny (i.e. module or module type), we tries to interprete this ast
   as a module, and in case of failure, as a module type. The returned
   kind is never ModAny, and it is equal to the input kind when this one
   isn't ModAny. *)

type module_kind = Module | ModType | ModAny

type module_struct_expr = (universe_decl_expr option * constr_expr) Declarations.module_alg_expr

(** Module internalization, i.e. from AST to module expression *)
val intern_module_ast :
  module_kind -> module_ast -> module_struct_expr * ModPath.t * module_kind

(** Module interpretation, i.e. from module expression to typed module entry *)
val interp_module_ast :
  env -> module_kind -> ModPath.t -> module_struct_expr -> module_struct_entry * Univ.ContextSet.t

(** Every module path named by a module expression interpreted so far in
    the library being compiled (binary-equivalence-taiga#841 round 23).
    [Declaremods.end_library] turns these into the library's structural
    dependencies: the libraries whose structure this one copies, and whose
    whole exported interface it therefore depends on. *)
val structural_targets : unit -> ModPath.t list

(** Forget them, so the next library compiled by this process starts with
    an empty record. Called by [Declaremods.end_library] once it has read
    them. *)
val clear_structural_targets : unit -> unit
