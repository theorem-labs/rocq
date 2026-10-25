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

let output_context = ref false

(* The summary's unsafe-flag sections fold over the final environment, which
   holds only the interface of a module sealed with [Module M : T]: a constant
   of the implementation is checked, yet it is absent there, so its unsafe
   flags would go unreported. The checker therefore records the flags of every
   constant and inductive it checks, implementations included, and the summary
   adds what the environment walk did not see. *)
type unsafe_flags = {
  type_in_type : string list;
  unchecked_eliminations : string list;
  unguarded : string list;
  nonpositive : string list;
  indices_matter : string list;
}

let empty_unsafe_flags = {
  type_in_type = [];
  unchecked_eliminations = [];
  unguarded = [];
  nonpositive = [];
  indices_matter = [];
}

let unsafe_flags = ref None

let start_summary enabled =
  unsafe_flags := if enabled then Some empty_unsafe_flags else None

let add_name name names =
  if List.mem name names then names else name :: names

let record_constant c cb =
  match !unsafe_flags with
  | None -> ()
  | Some flags ->
    let name = Constant.to_string c in
    unsafe_flags := Some {
      flags with
      type_in_type =
        if cb.const_typing_flags.check_universes then flags.type_in_type
        else add_name name flags.type_in_type;
      unchecked_eliminations =
        if cb.const_typing_flags.check_eliminations then flags.unchecked_eliminations
        else add_name name flags.unchecked_eliminations;
      unguarded =
        if cb.const_typing_flags.check_guarded then flags.unguarded
        else add_name name flags.unguarded;
    }

let record_inductive c mib =
  match !unsafe_flags with
  | None -> ()
  | Some flags ->
    let name = MutInd.to_string c in
    unsafe_flags := Some {
      type_in_type =
        if mib.mind_typing_flags.check_universes then flags.type_in_type
        else add_name name flags.type_in_type;
      unchecked_eliminations =
        if mib.mind_typing_flags.check_eliminations then flags.unchecked_eliminations
        else add_name name flags.unchecked_eliminations;
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

(* The environment walk keeps its own order, and the recorded names it already
   holds are dropped, so a constant is never listed twice. *)
let add_missing names extras =
  let rec collect extras = function
    | [] -> extras
    | name :: rest ->
      if List.mem name names || List.mem name extras then collect extras rest
      else collect (name :: extras) rest
  in
  match List.rev (collect [] (List.rev extras)) with
  | [] -> names
  | extras -> names @ extras

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
  let add c cb acc =
    if Declareops.constant_has_body cb then acc else
      match Cmap.find_opt c opac with
      | None -> Cset.add c acc
      | Some s -> Cset.union s acc in
  let csts = fold_constants add env Cset.empty in
  let csts = Cset.fold (fun c acc -> Constant.to_string c :: acc) csts [] in
  pr_assumptions "Axioms" csts

let pr_type_in_type env flags =
  let csts = fold_constants (fun c cb acc -> if not cb.const_typing_flags.check_universes then Constant.to_string c :: acc else acc) env [] in
  let csts = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_universes then MutInd.to_string c :: acc else acc) env csts in
  pr_assumptions "Constants/Inductives relying on type-in-type" (add_missing csts flags.type_in_type)

(* Kept out of the report when empty: this flag has no vernacular setter and
   should stay obscure (see #22294 discussion). *)
let pr_unchecked_eliminations env flags =
  let csts = fold_constants (fun c cb acc -> if not cb.const_typing_flags.check_eliminations then Constant.to_string c :: acc else acc) env [] in
  let csts = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_eliminations then MutInd.to_string c :: acc else acc) env csts in
  let csts = add_missing csts flags.unchecked_eliminations in
  if csts = [] then mt ()
  else str "* " ++ hov 0 (pr_assumptions "Constants/Inductives relying on unchecked sort eliminations" csts ++ fnl()) ++ fnl()

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

let print_context env opac =
  if !output_context then begin
    let flags = current_unsafe_flags () in
    Feedback.msg_notice
      (hov 0
      (fnl() ++ str"CONTEXT SUMMARY" ++ fnl() ++
      str"===============" ++ fnl() ++ fnl() ++
      str "* " ++ hov 0 (pr_impredicative_set env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_rewrite_rules env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_axioms env opac ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_type_in_type env flags ++ fnl()) ++ fnl() ++
      pr_unchecked_eliminations env flags ++
      str "* " ++ hov 0 (pr_unguarded env flags ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_nonpositive env flags ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_indices_matter env flags ++ fnl()))
      )
  end

let stats env opac =
  print_context env opac;
  print_memory_stat ()
