(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let available = false

type 'a t = |
let spawn _ = invalid_arg "CDomain.spawn: domains need OCaml 5"
let join (d : _ t) = match d with _ -> .

let self_index () = 0

module DLS = struct
  type 'a key = { init : unit -> 'a; mutable value : 'a option }
  let new_key init = { init; value = None }
  let get k = match k.value with
    | Some v -> v
    | None -> let v = k.init () in k.value <- Some v; v
  let set k v = k.value <- Some v
end
