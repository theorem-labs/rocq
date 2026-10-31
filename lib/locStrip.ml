(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

exception Unknown of string

let unknown what = raise (Unknown what)

let fixed = Loc.initial Loc.ToplevelInput

let loc _ = fixed

let loc_opt _ = None

let cast f x = CAst.make (f x.CAst.v)

let dast f x = DAst.make (f (DAst.get x))

let located f (_, x) = (None, f x)
