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

(* Records of the opacity a [Strategy]/[Transparent] command saw on a
   constant while a library is compiled (design D18, dispatch://INFRA-361,
   Astra review 2 blocker 1).

   [Tactics.Redexpr.check_not_fully_opaque] rejects a non-opaque strategy
   command (`Transparent c.`, `Strategy expand [c].`) on a constant [c] whose
   body is an opaque proof ([OpaqueDef]), but accepts it on an axiom
   ([Undef]). The library label v2b ([Vernac.LibkeyObjects]) deliberately gives
   an axiom and an opaque proof the same label, so an edit that completes an
   admitted dependency constant with a [Qed] proof keeps the dependency's
   label, yet a real recompile of a dependent that set a non-opaque strategy
   on that constant would now hit the error. A [local] strategy command (the
   default of [Opacity]) writes no persistent object, so a dependent's [.vo]
   does not record it. So the fact is logged here, outside the state a [Fail]
   rolls back, and [Vernac.Library] stores the foreign ones in the saved
   library ([KeepFacts]) for the keep rule to revalidate against the
   dependency's current opacity. A library that makes no such query gets no
   record, so its file is what a stock [coqc] writes. *)

let enabled = ref false

let set_enabled b = enabled := b

let queries : (Constant.t * bool) list ref = ref []

let reset () = queries := []

let record c ~opaque =
  if !enabled then queries := (c, opaque) :: !queries

let get () = !queries
