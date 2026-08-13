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

let proof_assumption_targets = ref []
let proof_assumptions_output = ref None

let json_string value =
  let out = Buffer.create (String.length value + 2) in
  Buffer.add_char out '"';
  String.iter (function
    | '"' -> Buffer.add_string out "\\\""
    | '\\' -> Buffer.add_string out "\\\\"
    | '\b' -> Buffer.add_string out "\\b"
    | '\012' -> Buffer.add_string out "\\f"
    | '\n' -> Buffer.add_string out "\\n"
    | '\r' -> Buffer.add_string out "\\r"
    | '\t' -> Buffer.add_string out "\\t"
    | c when Char.code c < 0x20 ->
      Buffer.add_string out (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char out c)
    value;
  Buffer.add_char out '"';
  Buffer.contents out

let find_constant constants target =
  match CString.Map.find_opt target constants with
  | Some kn -> kn
  | None ->
    CErrors.user_err
      Pp.(str "coqchk proof-assumptions target was not found: " ++ str target)

let proof_assumptions_json env opac targets =
  let constants =
    fold_constants
      (fun kn _ constants -> CString.Map.add (Constant.to_string kn) kn constants)
      env CString.Map.empty
  in
  let constants =
    Cmap.fold
      (fun kn _ constants -> CString.Map.add (Constant.to_string kn) kn constants)
      opac constants
  in
  let target_json target =
    let kn = find_constant constants target in
    let assumptions = Mod_checking.assumptions_of_constant env opac kn in
    let assumptions = Cset.fold (fun c acc -> Constant.to_string c :: acc) assumptions [] in
    let assumptions = List.sort String.compare assumptions in
    Printf.sprintf
      "{\"constant\":%s,\"assumptions\":[%s]}"
      (json_string target)
      (String.concat "," (List.map json_string assumptions))
  in
  let targets = List.sort_uniq String.compare targets in
  Printf.sprintf
    "{\"schema_version\":1,\"targets\":[%s]}\n"
    (String.concat "," (List.map target_json targets))

let write_proof_assumptions env opac =
  match !proof_assumption_targets, !proof_assumptions_output with
  | [], None -> ()
  | [], Some _ ->
    CErrors.user_err
      Pp.(str "--proof-assumptions-output requires at least one --proof-assumptions target")
  | _ :: _, None ->
    CErrors.user_err
      Pp.(str "--proof-assumptions requires --proof-assumptions-output")
  | targets, Some "-" ->
    output_string stdout (proof_assumptions_json env opac targets);
    flush stdout
  | targets, Some path ->
    let output = proof_assumptions_json env opac targets in
    let channel = open_out_bin path in
    try
      output_string channel output;
      close_out channel
    with error ->
      close_out_noerr channel;
      raise error

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

let pr_type_in_type env =
  let csts = fold_constants (fun c cb acc -> if not cb.const_typing_flags.check_universes then Constant.to_string c :: acc else acc) env [] in
  let csts = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_universes then MutInd.to_string c :: acc else acc) env csts in
  pr_assumptions "Constants/Inductives relying on type-in-type" csts

(* Kept out of the report when empty: this flag has no vernacular setter and
   should stay obscure (see #22294 discussion). *)
let pr_unchecked_eliminations env =
  let csts = fold_constants (fun c cb acc -> if not cb.const_typing_flags.check_eliminations then Constant.to_string c :: acc else acc) env [] in
  let csts = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_eliminations then MutInd.to_string c :: acc else acc) env csts in
  if csts = [] then mt ()
  else str "* " ++ hov 0 (pr_assumptions "Constants/Inductives relying on unchecked sort eliminations" csts ++ fnl()) ++ fnl()

let pr_unguarded env =
  let csts = fold_constants (fun c cb acc -> if not cb.const_typing_flags.check_guarded then Constant.to_string c :: acc else acc) env [] in
  let csts = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_guarded then MutInd.to_string c :: acc else acc) env csts in
  pr_assumptions "Constants/Inductives relying on unsafe (co)fixpoints" csts

let pr_nonpositive env =
  let inds = fold_inductives (fun c cb acc -> if not cb.mind_typing_flags.check_positive then MutInd.to_string c :: acc else acc) env [] in
  pr_assumptions "Inductives whose positivity is assumed" inds

let pr_indices_matter env =
  let inds = fold_inductives (fun c cb acc ->
    if cb.mind_typing_flags.indices_matter then acc
    else if Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) cb.mind_packets
    then MutInd.to_string c :: acc
    else acc) env [] in
  pr_assumptions "Inductives relying on indices not mattering" inds

let print_context env opac =
  if !output_context then begin
    Feedback.msg_notice
      (hov 0
      (fnl() ++ str"CONTEXT SUMMARY" ++ fnl() ++
      str"===============" ++ fnl() ++ fnl() ++
      str "* " ++ hov 0 (pr_impredicative_set env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_rewrite_rules env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_axioms env opac ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_type_in_type env ++ fnl()) ++ fnl() ++
      pr_unchecked_eliminations env ++
      str "* " ++ hov 0 (pr_unguarded env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_nonpositive env ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_indices_matter env ++ fnl()))
      )
  end

let stats env opac =
  print_context env opac;
  write_proof_assumptions env opac;
  print_memory_stat ()
