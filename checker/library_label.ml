(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* rocq-library-label: the location-free library label of a .vo file
   (vernac/libkeyObjects.ml), recomputed from the file's content.
   - [--check FILE.vo]: one line. "label2 <64 hex>" when the digest the file
     stores for its library segment is the first 16 bytes of the label
     (layout version 2) recomputed from the file's summary and library
     segments, followed by the whole 32-byte label; "md5 <32 hex>" when it
     is the MD5 of the segment's bytes (stock's digest: a library compiled
     without -location-free-label, or with no label), followed by it;
     "other <hex>" otherwise (a label of another layout version, a tampered
     file), followed by the stored digest.
   - [--stored FILE.vo]: the digest the file stores for its library segment,
     in hex, as its dependents record it.
   - [--attempts FILE.vo]: the attempted-resolution records (Attempts), one
     line each, or "no attempts".
   - [--attempts-json FILE.vo]: the same records as one JSON document, in
     the schema documented at [Attempts.to_json] (vernac/attempts.mli).
   Exit 0; 1 when the file cannot be read as a .vo file; 2 on a usage error;
   3 when --attempts-json meets a string that is not valid UTF-8.
   Every object kind of rocq's own plugins is linked in (-linkall), so the
   kinds a library uses are registered as they are in [rocq compile]. *)

let hex s =
  String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))

let usage () =
  prerr_endline "usage: rocq-library-label (--check | --stored | --attempts | --attempts-json) FILE.vo";
  exit 2

let read f =
  match Library.read_file_label f with
  | l -> l
  | exception e ->
    prerr_endline ("rocq-library-label: cannot read " ^ f ^ ": " ^ Printexc.to_string e);
    exit 1

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [mode; f] ->
    begin match mode with
    | "--check" ->
      let l = read f in
      begin match Lazy.force l.label with
      | Ok label when String.equal (Libkey.stored label) l.stored ->
        Printf.printf "label2 %s\n" (hex label)
      | Ok _ | Error _ ->
        if String.equal (Lazy.force l.segment_md5) l.stored then Printf.printf "md5 %s\n" (hex l.stored)
        else Printf.printf "other %s\n" (hex l.stored)
      end
    | "--stored" -> print_endline (hex (read f).stored)
    | "--attempts" ->
      begin match (read f).attempts with
      | None -> print_endline "no attempts"
      | Some t -> List.iter print_endline (Attempts.describe t)
      end
    | "--attempts-json" ->
      begin match Attempts.to_json (read f).attempts with
      | Ok j -> print_endline j
      | Error what -> prerr_endline ("rocq-library-label: " ^ f ^ ": " ^ what); exit 3
      end
    | _ -> usage ()
    end
  | _ -> usage ()
