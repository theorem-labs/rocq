(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let available = true

type 'a t = 'a Domain.t
let spawn f = Domain.spawn f
let join d = Domain.join d

let self_index () = (Domain.self () :> int)

module DLS = struct
  type 'a key = 'a Domain.DLS.key
  let new_key f = Domain.DLS.new_key f
  let get k = Domain.DLS.get k
  let set k v = Domain.DLS.set k v
end
