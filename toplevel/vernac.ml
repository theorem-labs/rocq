(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Parsing of vernacular. *)

open Pp
open CErrors
open Util
open Vernacexpr
open Vernacprop

(* The functions in this module may raise (unexplainable!) exceptions.
   Use the module Coqtoplevel, which catches these exceptions
   (the exceptions are explained only at the toplevel). *)

let checknav { CAst.loc; v = { expr } }  =
  if is_navigation_vernac expr && not (is_reset expr) then
    CErrors.user_err ?loc (str "Navigation commands forbidden in files.")

(* Echo from a buffer based on position.
   XXX: Should move to utility file. *)
let vernac_echo ?loc in_chan = let open Loc in
  Option.iter (fun loc ->
      let len = loc.ep - loc.bp in
      seek_in in_chan loc.bp;
      Feedback.msg_notice @@ str @@ really_input_string in_chan len
    ) loc


type time_output =
  | ToFeedback
  | ToChannel of Format.formatter

let make_time_output = function
  | Coqargs.ToFeedback -> ToFeedback
  | ToFile f ->
    let ch = open_out f in
    let fch = Format.formatter_of_out_channel ch in
    let close () =
      Format.pp_print_flush fch ();
      close_out ch
    in
    at_exit close;
    ToChannel fch

module State = struct

  type t = {
    doc : Stm.doc;
    sid : Stateid.t;
    proof : Proof.t option;
    time : time_output option;
  }

end

let emit_time state com tstart tend =
  match state.State.time with
  | None -> ()
  | Some time ->
    let pp = Topfmt.pr_cmd_header com ++ System.fmt_time_difference tstart tend in
    match time with
    | ToFeedback -> Feedback.msg_notice pp
    | ToChannel ch -> Pp.pp_with ch (pp ++ fnl())

let interp_vernac ~check ~state ({CAst.loc;_} as com) =
  let open State in
    try
      let doc, nsid, ntip = Stm.add ~doc:state.doc ~ontop:state.sid (not !Flags.quiet) com in

      (* Main STM interaction *)
      if ntip <> Stm.NewAddTip then
        anomaly (str "vernac.ml: We got an unfocus operation on the toplevel!");

      (* Force the command  *)
      let () = if check then Stm.observe ~doc nsid in
      let new_proof = Vernacstate.Declare.give_me_the_proof_opt () [@ocaml.warning "-3"] in
      { state with doc; sid = nsid; proof = new_proof; }
    with reraise ->
      let (reraise, info) = Exninfo.capture reraise in
      let info =
        (* Set the loc to the whole command if no loc *)
        match Loc.get_loc info, loc with
        | None, Some loc -> Loc.add_loc info loc
        | Some _, _ | _, None  -> info
      in
      Exninfo.iraise (reraise, info)

(* Load a vernac file. CErrors are annotated with file and location *)
let load_vernac_core ~echo ~check ~state ?source file =
  (* Keep in sync *)
  let in_chan = open_utf8_file_in file in
  let in_echo = if echo then Some (open_utf8_file_in file) else None in
  let input_cleanup () = close_in in_chan; Option.iter close_in in_echo in

  let source = Option.default (Loc.InFile {dirpath=None; file}) source in
  let in_pa = Procq.Parsable.make ~loc:Loc.(initial source)
      (Gramlib.Stream.of_channel in_chan) in
  let open State in

  (* One parsed sentence, run: everything the loop does once it has an
     AST. The replay path below runs buffered sentences through it too, so
     a proof that is not replayed is interpreted exactly as stock. *)
  let interp_one ~tstart state ast =
    (* BET-84: replay compares where a proof opens with the file's last late
       command (Proof_replay.start), and raises a replayed proof's warnings
       again relative to its statement, so it is told where each sentence is. *)
    Option.iter Proof_replay.at_sentence ast.CAst.loc;
    (* BET-84 P3: the charge for the proofs replay did not run is part of
       the file's clock, so a sentence that would carry the clock past the
       budget is stopped inside it, as stock's own timeout stops it, not
       only at the next sentence boundary. *)
    let interp_one () =
    try_finally
      (fun () ->
         NewProfile.profile "command"
           ~args:(fun () ->
               let lnum = match ast.CAst.loc with
                 | None -> "unknown"
                 | Some loc -> string_of_int loc.Loc.line_nb
               in
               [("cmd", `String (Pp.string_of_ppcmds (Topfmt.pr_cmd_header ast)));
                ("line", `String lnum)])
           (fun () ->
             (* BET-84: key item 1 is the parsed sentences of a proof, with
                the locations of this file removed. A sentence that is not
                a proof step is a command inside the proof (census row 21),
                which replay cannot make again. *)
             Proof_recorder.sentence
               ?span:(Option.map (fun loc -> (loc.Loc.bp, loc.Loc.ep)) ast.CAst.loc)
               (fun () -> Proof_recorder.digest ~locs:source ~what:"sentence" ast)
               (fun () ->
                  if Proof_recorder.active () then begin
                    match Vernac_classifier.classify_vernac ast with
                    | VtProofStep _ | VtQed _ | VtProofMode _ -> ()
                    | VtStartProof _ | VtSideff _ | VtQuery | VtMeta ->
                      Proof_recorder.ineligible ~reason:"command_in_proof"
                        ~detail:(Pp.string_of_ppcmds (Topfmt.pr_cmd_header ast))
                    | exception e when CErrors.noncritical e -> ()
                  end;
                  let v = Flags.silently (interp_vernac ~check ~state) ast in
                  (* The recorder is not part of [Vernacstate], so a command
                     that drops or restores the proof stack behind its back
                     ([Abort All], a reset, a rewind, [Fail]) would leave it
                     holding a proof that no longer exists, and every proof
                     after it in the file would be taken for a nested one and
                     lose its entry. One test a sentence catches that. With no
                     proof left there is no entry to mark, so what the recorder
                     holds is dropped and writes nothing; with other proofs
                     open but not the one it holds, the entry says that it
                     cannot be trusted. *)
                  (match Proof_recorder.current_name () with
                   | None -> ()
                   | Some held ->
                     (* This loop does not hold the interp state: the STM
                        installs it, and [interp_vernac] reads the top proof
                        from the same compatibility module. *)
                     match Vernacstate.Declare.get_all_proof_names () [@ocaml.warning "-3"] with
                     | [] when Proof_recorder.nested_closed () ->
                       (* The STM empties the stack after a nested proof's
                          closer and restores the proof around it at the
                          next command: that proof is still open. *)
                       ()
                     | [] ->
                       Proof_recorder.drop_all_proofs ();
                       Proof_record_env.drop_universe_frames ();
                       Proof_replay.abandon ()
                     | live ->
                       let base = match String.rindex_opt held '.' with
                         | None -> held
                         | Some i -> String.sub held (i + 1) (String.length held - i - 1)
                       in
                       if not (List.exists (fun id -> String.equal base (Names.Id.to_string id)) live)
                       then begin
                         Proof_recorder.ineligible ~reason:"recorder_desync"
                           ~detail:(held ^ " vs " ^ String.concat "," (List.map Names.Id.to_string live));
                         Proof_replay.abandon ()
                       end);
                  v)) ())
      ()
      (fun () ->
         let tend = System.get_time () in
         (* The -time option is only supported from console-based clients
            due to the way it prints. *)
         emit_time state ast tstart tend)
      ()
    in
    match Proof_replay.remaining_budget () with
    | None -> interp_one ()
    | Some left ->
      (match Control.timeout left interp_one () with
       | Ok v -> v
       | Error _ -> raise Proof_replay.Budget_exhausted)
  in

  let parse_next state =
    let tstart = System.get_time () in
    match
      NewProfile.profile "parse_command" (fun () ->
          Stm.parse_sentence
            ~doc:state.doc ~entry:Pvernac.main_entry state.sid in_pa)
        ()
    with
    | None -> None
    | Some ast ->
      (* Printing of AST for -compile-verbose *)
      Option.iter (vernac_echo ?loc:ast.CAst.loc) in_echo;
      checknav ast;
      Some (tstart, ast)
  in
  (* The same digest the recorder keeps for a sentence. A value it cannot
     digest gives a string no digest equals, so the proof misses. *)
  let sentence_digest ast =
    match Proof_record.digest_value ~locs:source ast with
    | d -> d
    | exception Proof_record.Unhashable _ -> "unhashable"
  in

  (* BET-84 P3. The record's key item 1 holds every sentence from the
     statement to the closer, so the decision cannot be taken before the
     closer is parsed, and it must be taken before a tactic runs. So, at a
     proof the record has an entry for, the sentences are parsed and kept
     until the closer, and interpreted only then: on a hit, the closer
     alone runs and declares the stored term; otherwise every kept
     sentence runs in order, exactly as stock.

     Parsing ahead is sound because nothing that changes the grammar is a
     proof step: a command inside a proof ends the buffering and is
     interpreted where stock interprets it. *)
  let closer_of ast =
    let open Vernacexpr in
    if ast.CAst.v.control <> [] then None
    else
      match ast.CAst.v.expr with
      | VernacSynPure (VernacEndProof Admitted) -> Some "Admitted"
      | VernacSynPure (VernacEndProof (Proved (Opaque, None))) -> Some "Qed"
      | VernacSynPure (VernacEndProof (Proved (Opaque, Some _))) -> Some "Save"
      | VernacSynPure (VernacEndProof (Proved (Transparent, _))) -> Some "Defined"
      | _ -> None
  in
  let proof_step ast =
    ast.CAst.v.Vernacexpr.control = []
    && (match Vernac_classifier.classify_vernac ast with
        (* A [Proof Mode] sentence changes the grammar the next sentences
           are parsed with, so it cannot be kept and run later: it ends
           the buffering and runs where stock runs it (review P3Deep F8). *)
        | VtProofStep _ -> true
        | VtProofMode _ | VtStartProof _ | VtQed _ | VtSideff _ | VtQuery | VtMeta -> false
        | exception e when CErrors.noncritical e -> false)
  in
  let run_kept state ids kept =
    List.fold_left
      (fun (state, ids) (tstart, ast) ->
         let state = interp_one ~tstart state ast in
         (state, state.sid :: ids))
      (state, ids) (List.rev kept)
  in
  (* Returns the state after the proof closed, and whether the file ended
     inside it. [kept] and [sentences] are newest first. *)
  let rec gather state ids kept sentences =
    match parse_next state with
    | None ->
      (* The file ends inside the proof. Stock fails on it; run what was
         kept so that it fails in the same place. *)
      Proof_replay.abandon ();
      let state, ids = run_kept state ids kept in
      (state, ids, true)
    | Some (tstart, ast) ->
      let digest = sentence_digest ast in
      (match closer_of ast with
       | Some closer ->
         let sentences = List.rev (digest :: sentences) in
         (match Proof_replay.decide ~sentences ~closer with
          | Some blob ->
            Proof_replay.set_pending (Some blob);
            let state =
              Fun.protect ~finally:(fun () -> Proof_replay.set_pending None)
                (fun () -> interp_one ~tstart state ast)
            in
            (state, state.sid :: ids, false)
          | None ->
            let state, ids = run_kept state ids kept in
            let state = interp_one ~tstart state ast in
            (state, state.sid :: ids, false))
       | None ->
         if proof_step ast then gather state ids ((tstart, ast) :: kept) (digest :: sentences)
         else begin
           (* A command inside the proof: no replay, and it runs where
              stock runs it. *)
           Proof_replay.abandon ();
           let state, ids = run_kept state ids kept in
           let state = interp_one ~tstart state ast in
           (state, state.sid :: ids, false)
         end)
  in

  (* ids = For beautify, list of parsed sids *)
  let rec loop state ids =
    Proof_replay.check_budget ();
    match parse_next state with
    | None ->
      input_cleanup ();
      state, ids, Procq.Parsable.comments in_pa
    | Some (tstart, ast) ->
      let state = interp_one ~tstart state ast in
      let ids = state.sid :: ids in
      if not (Proof_replay.candidate_open ()) then (loop [@ocaml.tailcall]) state ids
      else
        (* The statement's own sentence is the first of its proof's. *)
        let sentences = [ sentence_digest ast ] in
        let state, ids, eof = gather state ids [] sentences in
        if eof then begin
          input_cleanup ();
          state, ids, Procq.Parsable.comments in_pa
        end
        else (loop [@ocaml.tailcall]) state ids

  in
  try loop state []
  with any ->   (* whatever the exception *)
    let (e, info) = Exninfo.capture any in
    input_cleanup ();
    Exninfo.iraise (e, info)

let process_expr ~state loc_ast =
  try interp_vernac ~check:true ~state loc_ast
  with reraise ->
    let reraise, info = Exninfo.capture reraise in

    (* Exceptions don't carry enough state to print themselves (typically missing the nametab)
       so we need to print before resetting to an older state. See eg #16745 *)
    let reraise = UserError (CErrors.iprint (reraise, info)) in
    (* Keep just the loc in the info as it's printed separately *)
    let info = Option.cata (Loc.add_loc Exninfo.null) Exninfo.null (Loc.get_loc info) in

    ignore(Stm.edit_at ~doc:state.doc state.sid);
    Exninfo.iraise (reraise, info)

let process_expr ~state loc_ast =
  let tstart = System.get_time () in
  try_finally (fun () -> process_expr ~state loc_ast)
    ()
    (fun () ->
       let tend = System.get_time () in
       emit_time state loc_ast tstart tend)
    ()

(******************************************************************************)
(* Beautify-specific code                                                     *)
(******************************************************************************)

(* vernac parses the given stream, executes interpfun on the syntax tree it
 * parses, and is verbose on "primitives" commands if verbosely is true *)
let beautify_suffix = ".beautified"

let set_formatter_translator ch =
  let out s b e = output_substring ch s b e in
  let ft = Format.make_formatter out (fun () -> flush ch) in
  Format.pp_set_max_boxes ft max_int;
  ft

let pr_new_syntax ?loc ft_beautify ocom =
  let loc = Option.append loc (Option.bind ocom (fun x -> x.CAst.loc)) in
  let loc = Option.cata Loc.unloc (0,0) loc in
  let before = comment (Pputils.extract_comments (fst loc)) in
  let com = Option.cata (fun com -> Ppvernac.pr_vernac com ++ fnl()) (mt ()) ocom in
  let after = comment (Pputils.extract_comments (snd loc)) in
  if !Flags.beautify_file then
    (Pp.pp_with ft_beautify (hov 0 (before ++ com ++ after));
     Format.pp_print_flush ft_beautify ())
  else
    Feedback.msg_info (hov 4 (str"New Syntax:" ++ fnl() ++ (hov 0 com)))

(* load_vernac with beautify *)
let beautify_pass ~doc ~comments ~ids ~filename =
  let ft_beautify, close_beautify =
    if !Flags.beautify_file then
      let chan_beautify = open_out (filename^beautify_suffix) in
      set_formatter_translator chan_beautify, fun () -> close_out chan_beautify;
    else
      !Topfmt.std_ft, fun () -> ()
  in
  (* The interface to the comment printer is imperative, so we first
     set the comments, then we call print. This has to be done for
     each file. *)
  Pputils.beautify_comments := comments;
  List.iter (fun id -> pr_new_syntax ft_beautify (Stm.get_ast ~doc id)) ids;

  (* Is this called so comments at EOF are printed? *)
  pr_new_syntax ~loc:(Loc.make_loc (max_int,max_int)) ft_beautify None;
  close_beautify ()

(* Main driver for file loading. For now, we only do one beautify
   pass. *)
let load_vernac ~echo ~check ~state ?source filename =
  let ostate, ids, comments = load_vernac_core ~echo ~check ~state ?source filename in
  (* Pass for beautify *)
  if !Flags.beautify then beautify_pass ~doc:ostate.State.doc ~comments ~ids:(List.rev ids) ~filename;
  (* End pass *)
  ostate
