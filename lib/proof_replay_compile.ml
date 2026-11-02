(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let configure ~source ~ratio ~budget ~peak_limit_kb ~digest =
  Proof_recorder.set_in_use ();
  Proof_replay_record.configure ~source ~peak_limit_kb ~digest;
  Proof_replay.configure_clock ~ratio ~budget

let configured = Proof_replay_record.configured

let set_vo_path = Proof_replay_record.set_vo_path

let start ~library ~source ~toolchain =
  match Proof_replay_record.load ~library ~toolchain with
  | None -> ()
  | Some record ->
    let source_late () =
      match source with
      | None -> Ok None
      | Some path ->
        match Proof_replay_record.read_file path with
        | text -> Ok (Proof_replay_scan.late_events text)
        | exception (Sys_error _ | End_of_file) -> Error ()
    in
    Proof_replay.start ~record ~source_late ~toolchain

let summary_path_of_vo vo = Filename.remove_extension vo ^ ".proof-replay.json"

let write ~killed path =
  if configured () then begin
    let oc = open_out_bin path in
    Fun.protect ~finally:(fun () -> close_out_noerr oc)
      (fun () -> output_string oc (Proof_replay.summary ~killed))
  end

let write_summary path = write ~killed:false path
let killed_summary path = write ~killed:true path
