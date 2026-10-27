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

let valid_id id = Id.is_valid (Id.to_string id)

let valid_dirpath dp = List.for_all valid_id (DirPath.repr dp)

let valid_mbid mbid =
  let _, id, dp = MBId.repr mbid in
  valid_id id && valid_dirpath dp

let rec valid_modpath = function
  | ModPath.MPfile dp -> valid_dirpath dp
  | ModPath.MPbound mbid -> valid_mbid mbid
  | ModPath.MPdot (mp, label) -> valid_modpath mp && valid_id label

let valid_kername kn =
  let mp, label = KerName.repr kn in
  valid_modpath mp && valid_id label

let quote s = "\"" ^ String.escaped s ^ "\""
