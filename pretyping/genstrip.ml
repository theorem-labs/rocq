(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genarg

type 'glb strip_fun = 'glb -> 'glb

module StripObj =
struct
  type ('raw, 'glb, 'top) obj = 'glb strip_fun
  let name = "strip"
  let default _ = None
end

module Strip = Register (StripObj)

let register_strip0 = Strip.register0

let rec strip : type r g t. (r, g, t) genarg_type -> g strip_fun = function
  | ListArg wit -> List.map (strip wit)
  | OptArg wit -> Option.map (strip wit)
  | PairArg (wit1, wit2) ->
    let f1 = strip wit1 and f2 = strip wit2 in
    fun (x1, x2) -> (f1 x1, f2 x2)
  | ExtraArg tag as wit ->
    if Strip.mem wit then Strip.obj wit
    else fun _ -> LocStrip.unknown ("generic argument " ^ ArgT.repr tag)

let generic_strip (GenArg (Glbwit wit, v)) =
  in_gen (glbwit wit) (strip wit v)
