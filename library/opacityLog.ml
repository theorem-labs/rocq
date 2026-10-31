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

(* Records of whether a constant was an axiom or an opaque proof when a
   command whose outcome depends on that distinction ran while a library was
   compiled (design D18, dispatch://INFRA-361, Astra review 2 blocker 1).

   The observers, each of which logs here before it decides:
   - [Tactics.Redexpr.check_not_fully_opaque] rejects a non-opaque strategy
     command (`Transparent c.`, `Strategy expand [c].`) on a constant [c]
     whose body is an opaque proof ([OpaqueDef]), but accepts it on an axiom
     ([Undef]);
   - extraction warns about an axiom to realize, or about an opaque proof it
     accessed, and either warning can be an error
     ([Extraction.extract_constant]);
   - [Functional Scheme] makes the principle it generates an opaque proof
     when the function's equation lemma is one, and a transparent definition
     otherwise ([Gen_principle.make_scheme]);
   - [Global.body_of_constant], the plugin API for a constant's body, answers
     [None] for an axiom and the forced body for an opaque proof.
   (The sweep of every other reader in the tree and in the plugins the BET
   image installs is design D18's observer sweep.) The library label
   ([Vernac.LibkeyObjects]) deliberately gives an axiom and an opaque proof
   of the library's own signature the same label, so an edit that completes
   an admitted dependency constant with a [Qed] proof keeps the dependency's
   label, yet a real
   recompile of a dependent that ran such a command on that constant could
   now fail, or stop failing. A [local] strategy command (the default of
   [Opacity]) writes no persistent object, so a dependent's [.vo] does not
   record it. So the fact is logged here, outside the state a [Fail] rolls
   back, and [Vernac.Library] stores the foreign ones in the saved library
   ([KeepFacts]) for the keep rule to revalidate against the dependency's
   current status. Only a constant whose body is [Undef None] or [OpaqueDef]
   is logged: those are the two forms the label blinds into one, and a
   constant of any other form cannot become the other kind while the label
   stays equal, so a record of it could only make the keep rule rebuild a
   dependent forever (`Transparent Nat.add.` on a transparent definition). A
   library that makes no such query gets no record, so its file is what a
   stock [coqc] writes.

   An extraction with AccessOpaque (the default) also reads an opaque proof's
   BODY, and what it extracts depends on that body, which no label covers; so
   does [Global.body_of_constant]'s caller, and the walk that computes a
   library's assumption closures ([KeepFacts]), whose result is stored. Such a
   read is logged with the library whose opaque table it read
   ([record_body_read]): for a copy that a
   module operation did not strengthen (a functor application, an [Include]
   of one, at any depth, a sealed module whose implementation is such an
   expression) that table's library can differ from the one holding the
   constant read. The library's [foreign_opaque_libraries]
   ([LibkeyObjects.axiom_report]) names it only for a copy whose [Indirect]
   reference the compiled form keeps, not for one read from a sealed
   module's expression. *)

let enabled = ref false

let set_enabled b = enabled := b

let queries : (Constant.t * bool * DirPath.t option) list ref = ref []

let reset () = queries := []

let record c (cb : Declarations.constant_body) =
  if !enabled then
    match cb.Declarations.const_body with
    | Declarations.Undef None -> queries := (c, false, None) :: !queries
    | Declarations.OpaqueDef _ -> queries := (c, true, None) :: !queries
    | Declarations.Undef (Some _) | Declarations.Def _
    | Declarations.Primitive _ | Declarations.Symbol _ -> ()

let record_body_read c o =
  if !enabled then
    let (_, _, dp, _) = Opaqueproof.repr o in
    queries := (c, true, Some dp) :: !queries

let get () = !queries
