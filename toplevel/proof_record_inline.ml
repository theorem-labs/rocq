(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let usage = "Usage: rocq proof-record-inline RECORD VO OUT\n\
\n\
Write to OUT the proof record RECORD with every stored term that refers to\n\
the opaque proofs of the object file VO put back inline, and the trailer's\n\
vo_opaques set to null. VO is the object the record was written beside.\n\
A record that another rocq binary wrote is refused. No proof line is\n\
dropped: remove the lines of proofs that must not ship before this.\n\
OUT may be RECORD. On an error, nothing is written.\n"

let fail fmt = Printf.kfprintf (fun _ -> exit 1) stderr ("rocq proof-record-inline: " ^^ fmt ^^ "\n%!")

let read path =
  try In_channel.with_open_bin path In_channel.input_all
  with Sys_error why -> fail "%s" why

(* The output appears whole or not at all: it is written beside OUT and
   renamed over it. *)
let write path data =
  let dir = Filename.dirname path in
  match Filename.temp_file ~temp_dir:dir ".proof-record-inline" ".tmp" with
  | exception Sys_error why -> fail "%s" why
  | tmp ->
    (try
       Out_channel.with_open_bin tmp (fun oc -> Out_channel.output_string oc data);
       Sys.rename tmp path
     with Sys_error why ->
       (try Sys.remove tmp with Sys_error _ -> ());
       fail "%s" why)

let main = function
  | [ ("-h" | "-help" | "--help") ] -> print_string usage; exit 0
  | [ record; vo; out ] ->
    (match Declare.inline_proof_record ~record:(read record) ~vo with
     | Ok data -> write out data
     | Error why -> fail "%s: %s" record why)
  | _ -> prerr_string usage; exit 2
