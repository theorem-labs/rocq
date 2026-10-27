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

(* An admitted library is never walked, and the environment holds only the
   interface of its sealed modules, so the sections below cannot see an unsafe
   flag inside one. Saying so beats printing <none>, which a reader takes for
   "nothing unsafe here". *)
let admitted = ref []

let record_admitted name =
  if !unsafe_flags <> None then admitted := name :: !admitted

(* Printed after the last section, with the blank line that separates
   sections, so that a summary with no admitted library is byte for byte what
   it was before this list existed. *)
let pr_admitted () = match List.rev !admitted with
  | [] -> mt ()
  | libs ->
    fnl() ++ str "* " ++
    hv 2 (str "Libraries admitted without checking, so the sections above cannot \
               see unsafe flags inside their sealed modules:" ++ fnl() ++
          prlist_with_sep fnl str libs) ++ fnl() ++ fnl()

(* A field of a functor parameter has no name of its own: [Constant.to_string]
   prints the parameter [X] as if it were a module, so [F (X : T)] and
   [G (X : T)] would both give [X.c] and could be mistaken for a real [X.c] of
   the library. Such a field is still checked under its own typing flags (a
   tampered library can put an unsafe definition in a parameter's signature),
   so it is listed, under the kernel's unambiguous name for the parameter,
   [<library#X#n>.c]. *)
let rec under_bound_module mp = match mp with
  | ModPath.MPbound _ -> true
  | ModPath.MPdot (mp, _) -> under_bound_module mp
  | ModPath.MPfile _ -> false

let constant_name c =
  if under_bound_module (Constant.modpath c) then KerName.debug_to_string (Constant.user c)
  else Constant.to_string c

let mind_name c =
  if under_bound_module (MutInd.modpath c) then KerName.debug_to_string (MutInd.user c)
  else MutInd.to_string c

(* Each list is built in reverse and deduplicated at print time, so recording
   a constant costs one cons rather than a scan of everything recorded. *)
let add_name name names = name :: names

let record_constant c cb =
  match !unsafe_flags with
  | None -> ()
  | Some flags ->
    let tf = cb.const_typing_flags in
    (* Most constants carry no unsafe flag; build nothing for them. *)
    if tf.check_universes && tf.check_eliminations && tf.check_guarded then () else
    let name = constant_name c in
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

(* [indices_matter] is the checker's own setting. checkFlags.ml checks every
   inductive under it and ignores the flag stored with the inductive, so the
   stored flag must not decide what is reported either. *)
let record_inductive ~indices_matter c mib =
  match !unsafe_flags with
  | None -> ()
  | Some flags ->
    let tf = mib.mind_typing_flags in
    let relies_on_indices =
      not indices_matter &&
      Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) mib.mind_packets
    in
    if tf.check_universes && tf.check_eliminations && tf.check_guarded
       && tf.check_positive && not relies_on_indices then () else
    let name = mind_name c in
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
        if relies_on_indices then add_name name flags.indices_matter
        else flags.indices_matter;
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

(* The fold also covers libraries that were admitted rather than checked, whose
   stored flag is all that is known of them, so a global [-indices-matter] must
   not clear their warning. A declaration is quiet only when both flags say
   indices mattered. The recorder above is not in that position: every entry it
   sees is being checked under the global flag. *)
let pr_indices_matter env flags =
  let indices_matter = (Environ.typing_flags env).indices_matter in
  let inds = fold_inductives (fun c cb acc ->
    if indices_matter && cb.mind_typing_flags.indices_matter then acc
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
      str "* " ++ hov 0 (pr_indices_matter env flags ++ fnl()) ++
      pr_admitted ())
      )
  end

let stats env opac =
  print_context env opac;
  print_memory_stat ()
