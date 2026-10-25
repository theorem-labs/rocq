(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coqargs
open Coqcargs
open Common_compile

(******************************************************************************)
(* File Compilation                                                           *)
(******************************************************************************)

let source ldir file = Loc.InFile {
    dirpath=Some (Names.DirPath.to_string ldir);
    file = file;
  }

(* Compile a vernac file *)
let compile opts stm_options injections copts ~echo ~f_in ~f_out =
  let open Vernac.State in
  let output_native_objects = match opts.config.native_compiler with
    | NativeOff -> false | NativeOn {ondemand} -> not ondemand
  in
  let mode = copts.compilation_mode in
  let ext_in, ext_out =
     match mode with
     | BuildVo -> ".v", ".vo"
     | BuildVos -> ".v", ".vos"
     | BuildVok -> ".v", ".vok"
  in
  let long_f_dot_in, long_f_dot_out =
    ensure_exists_with_prefix ~src:f_in ~tgt:f_out ~src_ext:ext_in ~tgt_ext:ext_out in
  match mode with
  | BuildVo | BuildVok ->
      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc
          Stm.{ doc_type = VoDoc long_f_dot_out; injections; } in
      let state = { doc; sid; proof = None; time = Option.map Vernac.make_time_output opts.config.time } in
      let state = Load.load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      Aux_file.(start_aux_file
        ~aux_file:(aux_file_name_for long_f_dot_out)
        ~v_file:long_f_dot_in);

      let dump = match copts.glob_out with
      | None -> Dumpglob.MultFiles { vofile = long_f_dot_out; vfile = long_f_dot_in }
      | Some NoGlob -> Dumpglob.NoGlob
      | Some (GlobFile f) -> Dumpglob.File f
      in
      Dumpglob.push_output dump;
      Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n");

      (* The record covers the proofs of this file only, so it starts after
         the prelude and the init vernaculars are loaded. *)
      let () = if copts.proof_record then
          Proof_recorder.start
            ~library:(Names.DirPath.to_string ldir)
            ~source:long_f_dot_in
            ~source_digest:(match Digest.file long_f_dot_in with
                | d -> Digest.to_hex d
                | exception Sys_error _ -> "unknown")
            ~toolchain:Proof_record_env.toolchain
            ~skip_qed_typecheck:!Opaques.skip_qed_typecheck
            ~tables_at_start:true
      in
      (* BET-84 P3: the registration's record for this library, and the
         charged clock. A record that is missing or was made under a limit
         this compile cannot match leaves the file to its tactics, which
         the summary says. *)
      let () = match copts.proof_replay with
        | None -> ()
        | Some source ->
          Proof_replay_env.init ();
          Proof_replay.configure ~source
            ~ratio:(Option.get copts.proof_replay_ratio)
            ~budget:copts.proof_replay_budget
            ~peak_limit_kb:copts.proof_replay_peak_limit_kb;
          Proof_replay.set_vo_path long_f_dot_out;
          Proof_replay.start ~library:(Names.DirPath.to_string ldir)
      in
      let wall_clock1 = Unix.gettimeofday () in
      let check = Stm.AsyncOpts.(stm_options.async_proofs_mode = APoff) in
      let source = source ldir long_f_dot_in in
      let state =
        try Vernac.load_vernac ~echo ~check ~state ~source long_f_dot_in with
        | Proof_replay.Budget_exhausted ->
          (* BET-84 P3: the real time plus the charge for the proofs replay
             did not run has reached the file's budget. The file ends as
             stock's own timeout ends it: no .vo, and the exit code the
             engine's wrapper records as a per-file kill. *)
          Proof_replay.killed_summary (Proof_replay.summary_path_of_vo long_f_dot_out);
          prerr_endline "KILLED: proof replay charged clock reached the per-file budget";
          flush stderr;
          exit 124
      in
      let fullstate = Stm.finish ~doc:state.doc in
      ensure_no_pending_proofs ~filename:long_f_dot_in fullstate;
      let () = Stm.join ~doc:state.doc in
      let wall_clock2 = Unix.gettimeofday () in
      (* In .vo production, dump a complete .vo file. *)
      let () = if mode = BuildVo then
          Library.save_library_to ~output_native_objects Library.ProofsTodoNone ldir long_f_dot_out
      in
      (* After the .vo: a compile that fails or is killed leaves no record. *)
      let () = if copts.proof_record then
          Proof_recorder.write (Proof_record.path_of_vo long_f_dot_out)
      in
      let () = Proof_replay.write_summary (Proof_replay.summary_path_of_vo long_f_dot_out) in
      let () = Aux_file.record_in_aux_at "vo_compile_time"
          (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1))
      in
      let () = Aux_file.stop_aux_file () in
      ()

  | BuildVos ->
      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc
          Stm.{ doc_type = VosDoc long_f_dot_out; injections;
              } in

      let state = { doc; sid; proof = None; time = Option.map Vernac.make_time_output opts.config.time } in
      let state = Load.load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      let source = source ldir long_f_dot_in in
      let state = Vernac.load_vernac ~echo ~check:false ~source ~state long_f_dot_in in
      let state = Stm.finish ~doc:state.doc in
      ensure_no_pending_proofs state ~filename:long_f_dot_in;
      let () = Stm.snapshot_vos ~doc ~output_native_objects ldir long_f_dot_out in
      Stm.reset_task_queue ();
      ()

let compile opts stm_opts copts injections ~echo ~f_in ~f_out =
  ignore(CoqworkmgrApi.get 1);
  compile opts stm_opts injections copts ~echo ~f_in ~f_out;
  CoqworkmgrApi.giveback 1

let compile_file opts stm_opts copts injections (f_in, echo) =
  let f_out = copts.compilation_output_name in
  if !Flags.beautify then
    Flags.with_option Flags.beautify_file
      (fun f_in -> compile opts stm_opts copts injections ~echo ~f_in ~f_out) f_in
  else
    compile opts stm_opts copts injections ~echo ~f_in ~f_out

let compile_file opts stm_opts copts injections =
  Option.iter (compile_file opts stm_opts copts injections) copts.compile_file
