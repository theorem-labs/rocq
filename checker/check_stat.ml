(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names
open Declarations
open Environ

let memory_stat = ref false

let print_memory_stat () =
  if !memory_stat then begin
    Format.printf "total heap size = %d kbytes\n" (CObj.heap_size_kb ());
    Format.print_newline();
    Format.print_flush()
  end

type unsafe_flags = {
  type_in_type : string list;
  unguarded : string list;
  nonpositive : string list;
  indices_matter : string list;
}

let empty_unsafe_flags = {
  type_in_type = [];
  unguarded = [];
  nonpositive = [];
  indices_matter = [];
}

let unsafe_flags = ref None

let start_summary enabled =
  unsafe_flags := if enabled then Some empty_unsafe_flags else None

(* An admitted library is never walked, and the environment holds only the
   interface of its sealed modules, so the sections below cannot see an unsafe
   flag inside one. Saying so beats printing <none>, which a reader takes for
   "nothing unsafe here". *)
let admitted = ref []

let record_admitted name =
  if !unsafe_flags <> None then admitted := name :: !admitted

let pr_admitted () = match List.rev !admitted with
  | [] -> mt ()
  | libs ->
    str "* " ++
    hv 2 (str "Libraries admitted without checking, so the sections above cannot \
               see unsafe flags inside their sealed modules:" ++ fnl() ++
          prlist_with_sep fnl str libs) ++ fnl() ++ fnl()

(* A name under a functor parameter would print as if it were a real constant
   of the library ([F(X:T)] and [G(X:T)] both give [X.c]), so the parameter's
   own fields are left to the functor's applications, which are checked in
   their own right. *)
let rec under_bound_module mp = match mp with
  | ModPath.MPbound _ -> true
  | ModPath.MPdot (mp, _) -> under_bound_module mp
  | ModPath.MPfile _ -> false

(* Each list is built in reverse and deduplicated at print time, so recording
   a constant costs one cons rather than a scan of everything recorded. *)
let add_name name names = name :: names

let record_constant c cb =
  match !unsafe_flags with
  | None -> ()
  | Some flags ->
    if under_bound_module (Constant.modpath c) then () else
    let name = Constant.to_string c in
    unsafe_flags := Some {
      flags with
      type_in_type =
        if cb.const_typing_flags.check_universes then flags.type_in_type
        else add_name name flags.type_in_type;
      unguarded =
        if cb.const_typing_flags.check_guarded then flags.unguarded
        else add_name name flags.unguarded;
    }

let record_inductive c mib =
  match !unsafe_flags with
  | None -> ()
  | Some flags ->
    if under_bound_module (MutInd.modpath c) then () else
    let name = MutInd.to_string c in
    unsafe_flags := Some {
      type_in_type =
        if mib.mind_typing_flags.check_universes then flags.type_in_type
        else add_name name flags.type_in_type;
      unguarded =
        if mib.mind_typing_flags.check_guarded then flags.unguarded
        else add_name name flags.unguarded;
      nonpositive =
        if mib.mind_typing_flags.check_positive then flags.nonpositive
        else add_name name flags.nonpositive;
      indices_matter =
        if mib.mind_typing_flags.indices_matter ||
           not (Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) mib.mind_packets)
        then flags.indices_matter
        else add_name name flags.indices_matter;
    }

(* The environment walk keeps its own order, and a recorded name it already
   holds is dropped, so a constant is never listed twice. The membership test
   is a set, because a tree can record tens of thousands of names. *)
let add_missing names extras =
  let seen = List.fold_left (fun s name -> CString.Set.add name s) CString.Set.empty names in
  let add (seen, acc) name =
    if CString.Set.mem name seen then (seen, acc)
    else (CString.Set.add name seen, name :: acc)
  in
  match snd (List.fold_left add (seen, []) (List.rev extras)) with
  | [] -> names
  | extras -> names @ List.rev extras

let current_unsafe_flags () =
  match !unsafe_flags with
  | None -> empty_unsafe_flags
  | Some flags -> flags

let pr_impredicative_set env =
  if is_impredicative_set env then str "Theory: Set is impredicative"
  else str "Theory: Set is predicative"

let pr_rewrite_rules env =
  if rewrite_rules_allowed env then str "Theory: Rewrite rules are allowed (consistency, subject reduction, confluence and normalization might be broken)"
  else str "Theory: Rewrite rules are not allowed"

let pr_assumptions ass axs =
  if axs = [] then
    str ass ++ str ": <none>"
  else
    hv 2 (str ass ++ str ":" ++ fnl() ++ prlist_with_sep fnl str axs)

let pr_axioms env opac =
  let csts = List.map Constant.to_string opac in
  pr_assumptions "Axioms" csts

let pr_type_in_type env flags =
  let csts = fold_constants (fun c cb acc -> if not cb.const_typing_flags.check_universes then Constant.to_string c :: acc else acc) env [] in
  let csts = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_universes then MutInd.to_string c :: acc else acc) env csts in
  pr_assumptions "Constants/Inductives relying on type-in-type" (add_missing csts flags.type_in_type)

let pr_unguarded env flags =
  let csts = fold_constants (fun c cb acc -> if not cb.const_typing_flags.check_guarded then Constant.to_string c :: acc else acc) env [] in
  let csts = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_guarded then MutInd.to_string c :: acc else acc) env csts in
  pr_assumptions "Constants/Inductives relying on unsafe (co)fixpoints" (add_missing csts flags.unguarded)

let pr_nonpositive env flags =
  let inds = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_positive then MutInd.to_string c :: acc else acc) env [] in
  pr_assumptions "Inductives whose positivity is assumed" (add_missing inds flags.nonpositive)

let pr_indices_matter env flags =
  let inds = fold_inductives (fun c cb acc ->
    if cb.mind_typing_flags.indices_matter then acc
    else if Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) cb.mind_packets
    then MutInd.to_string c :: acc
    else acc) env [] in
  pr_assumptions "Inductives relying on indices not mattering" (add_missing inds flags.indices_matter)

let print_context env opac = match opac with
| None -> ()
| Some opac ->
  let flags = current_unsafe_flags () in
  Feedback.msg_notice
    (hov 0
    (fnl() ++ str"CONTEXT SUMMARY" ++ fnl() ++
    str"===============" ++ fnl() ++ fnl() ++
    str "* " ++ hov 0 (pr_impredicative_set env ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_rewrite_rules env ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_axioms env opac ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_type_in_type env flags ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_unguarded env flags ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_nonpositive env flags ++ fnl()) ++ fnl() ++
    str "* " ++ hov 0 (pr_indices_matter env flags ++ fnl()) ++ fnl() ++
    pr_admitted ())
    )

let stats env opac =
  print_context env opac;
  print_memory_stat ()
