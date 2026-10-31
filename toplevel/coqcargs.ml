(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type compilation_mode = BuildVo | BuildVos | BuildVok

type glob_output =
| NoGlob
| GlobFile of string              (* Single file for all coqc arguments *)

type t =
  { compilation_mode : compilation_mode

  ; compile_file: (string * bool) option  (* bool is verbosity  *)
  ; compilation_output_name : string option

  ; echo : bool

  ; glob_out    : glob_output option

  ; proof_record : bool
  ; proof_record_no_graph : bool
  ; proof_record_vo_ref : bool

  ; proof_replay : Proof_replay.source option
  ; proof_replay_ratio : float option
  ; proof_replay_budget : float option
  ; proof_replay_peak_limit_kb : int option
  ; proof_replay_digest : string option

  ; output_context : bool
  }

let default =
  { compilation_mode = BuildVo

  ; compile_file = None
  ; compilation_output_name = None

  ; echo = false

  ; glob_out = None

  ; proof_record = false
  ; proof_record_no_graph = false
  ; proof_record_vo_ref = false

  ; proof_replay = None
  ; proof_replay_ratio = None
  ; proof_replay_budget = None
  ; proof_replay_peak_limit_kb = None
  ; proof_replay_digest = None

  ; output_context = false
  }

let depr opt =
  Feedback.msg_warning Pp.(seq[str "Option "; str opt; str " is a noop and deprecated"])

(* XXX Remove this duplication with Coqargs *)
let fatal_error exn =
  Topfmt.(in_phase ~phase:ParsingCommandLine print_err_exn exn);
  let exit_code = CErrors.exit_code exn in
  exit exit_code

let error_missing_arg s =
  prerr_endline ("Error: extra argument expected after option "^s);
  prerr_endline "See -help for the syntax of supported options";
  exit 1

let arg_error msg = CErrors.user_err msg

let is_dash_argument s = String.length s > 0 && s.[0] = '-'

let add_compile ?echo copts s =
  if is_dash_argument s then
    arg_error Pp.(str "Unknown option " ++ str s);
  (* make the file name explicit; needed not to break up Rocq loadpath stuff. *)
  let echo = Option.default copts.echo echo in
  let s =
    let open Filename in
    if is_implicit s
    then concat current_dir_name s
    else s
  in
  { copts with compile_file = Some (s,echo) }

let add_compile ?echo copts v_file =
  match copts.compile_file with
  | Some (first,_) ->
    arg_error Pp.(str "More than one file to compile: " ++ str first ++ spc() ++
                  str "and " ++ str v_file)
  | None ->
    add_compile ?echo copts v_file

let parse arglist : t =
  let echo = ref false in
  let args = ref arglist in
  let extras = ref [] in
  let rec parse (oval : t) = match !args with
    | [] ->
      (oval, List.rev !extras)
    | opt :: rem ->
      args := rem;
      let next () = match !args with
        | x::rem -> args := rem; x
        | [] -> error_missing_arg opt
      in
      let noval : t = begin match opt with
        (* Deprecated options *)
        | "-opt"
        | "-byte" as opt ->
          depr opt;
          oval
        | "-image" as opt ->
          depr opt;
          let _ = next () in
          oval

        (* Non deprecated options *)
        | "-output-context" ->
          { oval with output_context = true }
        (* Verbose == echo mode *)
        | "-verbose" ->
          echo := true;
          oval
        (* Output filename *)
        | "-o" ->
          { oval with compilation_output_name = Some (next ()) }
        |"-vos" ->
          Loadpath.load_vos_libraries := true;
          { oval with compilation_mode = BuildVos }
        |"-vok" ->
          Loadpath.load_vos_libraries := true;
          { oval with compilation_mode = BuildVok }

        (* Glob options *)
        |"-no-glob" | "-noglob" ->
          { oval with glob_out = Some NoGlob }

        |"-dump-glob" ->
          let file = next () in
          { oval with glob_out = Some (GlobFile file) }

        (* Per-proof record (BET-84 P2) and replay (P3) *)
        |"-proof-record" ->
          { oval with proof_record = true }
        |"-proof-record-no-graph" ->
          { oval with proof_record_no_graph = true }
        |"-proof-record-vo-ref" ->
          { oval with proof_record_vo_ref = true }
        |"-proof-replay" ->
          { oval with proof_replay = Some (Proof_replay.Record_file (next ())) }
        |"-proof-replay-dir" ->
          { oval with proof_replay = Some (Proof_replay.Record_dir (next ())) }
        |"-proof-replay-ratio" ->
          let s = next () in
          (match float_of_string_opt s with
           | Some r when r > 0. && Float.is_finite r -> { oval with proof_replay_ratio = Some r }
           | _ -> arg_error Pp.(str "-proof-replay-ratio expects a positive number, not " ++ str s))
        |"-proof-replay-budget" ->
          let s = next () in
          (match float_of_string_opt s with
           | Some b when b > 0. && Float.is_finite b -> { oval with proof_replay_budget = Some b }
           | _ -> arg_error Pp.(str "-proof-replay-budget expects a positive number of seconds, not " ++ str s))
        |"-proof-replay-peak-limit-kb" ->
          let s = next () in
          (match int_of_string_opt s with
           | Some k when k > 0 -> { oval with proof_replay_peak_limit_kb = Some k }
           | _ -> arg_error Pp.(str "-proof-replay-peak-limit-kb expects a positive integer, not " ++ str s))
        |"-proof-replay-digest" ->
          let s = String.lowercase_ascii (next ()) in
          let hex c = (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') in
          if String.length s = 64 && String.for_all hex s then { oval with proof_replay_digest = Some s }
          else arg_error Pp.(str "-proof-replay-digest expects a SHA-256 as 64 hex digits, not " ++ str s)

        (* Rest *)
        | s ->
          extras := s :: !extras;
          oval
      end in
      parse noval
  in
  try
    let opts, extra = parse default in
    (* BET-84 P3: replay charges each replayed proof r times its registered
       wall seconds. There is no default r, because a charge that is too
       small lets a file pass that stock's own timeout kills. *)
    (match opts.proof_replay, opts.proof_replay_ratio with
     | Some _, None ->
       arg_error
         Pp.(str "-proof-replay needs -proof-replay-ratio: the grade-to-registration ratio of per-file "
             ++ str "wall time, at the top of its measured spread. Replay is refused without it.")
     | None, Some _ ->
       arg_error Pp.(str "-proof-replay-ratio was given without -proof-replay.")
     | Some _, Some _ | None, None -> ());
    (* A compile that replays writes a record that names terms it never
       built, and its evaluators would read into it (review P3Deep F9).
       The two options are for two different compiles. *)
    if opts.proof_replay <> None && opts.proof_record then
      arg_error Pp.(str "-proof-record and -proof-replay cannot be used together.");
    if opts.proof_replay_digest <> None && opts.proof_replay = None then
      arg_error Pp.(str "-proof-replay-digest was given without -proof-replay.");
    if (opts.proof_record_no_graph || opts.proof_record_vo_ref) && not opts.proof_record then
      arg_error Pp.(str "-proof-record-no-graph and -proof-record-vo-ref need -proof-record.");
    (* The record is a trusted input, used only when its bytes hash to a
       digest the caller took from a trusted place (reviews P3Deep F1,
       P3Bugs). A directory of records carries one [.sha256] beside each. *)
    (match opts.proof_replay, opts.proof_replay_digest with
     | Some (Proof_replay.Record_file _), None ->
       arg_error Pp.(str "-proof-replay needs -proof-replay-digest: the SHA-256 of the record, from the "
                     ++ str "registration's manifest. Replay is refused without it.")
     | _ -> ());
    let args = List.fold_left add_compile opts extra in
    args
  with any -> fatal_error any
