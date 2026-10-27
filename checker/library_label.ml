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
   - [--axiom-report-json FILE.vo]: one JSON document for the keep rule's
     monotone axiom condition (schema "rocq-library-label/axiom-report",
     version 1): the library name, the label kind and the hex [--check]
     prints, the constants whose label contribution the axiom-or-opaque
     blinding erased (each with its current "axiom" or "proof" status), and
     the libraries this one holds a foreign opaque reference into.
   Exit 0; 1 when the file cannot be read as a .vo file; 2 on a usage error;
   3 when --attempts-json meets a string that is not valid UTF-8.
   Every object kind of rocq's own plugins is linked in (-linkall), so the
   kinds a library uses are registered as they are in [rocq compile]. *)

let hex s =
  String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))

let usage () =
  prerr_endline "usage: rocq-library-label (--check | --stored | --attempts | --attempts-json | --axiom-report-json) FILE.vo";
  exit 2

(* The label kind [--check] prints, and the hex it prints beside it: the full
   32-byte label for [label2], otherwise the stored digest. *)
let check_kind (l : Library.file_label) =
  match Lazy.force l.label with
  | Ok label when String.equal (Libkey.stored label) l.stored -> ("label2", hex label)
  | Ok _ | Error _ ->
    if String.equal (Lazy.force l.segment_md5) l.stored then ("md5", hex l.stored)
    else ("other", hex l.stored)

(* A JSON string: the small ASCII identifiers and dotted paths here never need
   more, but quotes, backslashes and controls are escaped so a surprising name
   cannot break the document. *)
let json_string b s =
  Buffer.add_char b '"';
  String.iter (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | c when Char.code c < 0x20 -> Printf.bprintf b "\\u%04x" (Char.code c)
      | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"'

let axiom_report_json (l : Library.file_label) =
  let r = Lazy.force l.axiom_report in
  let kind, lhex = check_kind l in
  let b = Buffer.create 1024 in
  let comma = ref false in
  let field k f = (if !comma then Buffer.add_char b ','); comma := true;
    json_string b k; Buffer.add_char b ':'; f () in
  Buffer.add_char b '{';
  field "schema" (fun () -> json_string b "rocq-library-label/axiom-report");
  field "version" (fun () -> Buffer.add_string b "1");
  field "library" (fun () -> json_string b (Names.DirPath.to_string l.name));
  field "label_kind" (fun () -> json_string b kind);
  field "label" (fun () -> json_string b lhex);
  field "axiom_blind" (fun () ->
      Buffer.add_char b '[';
      List.iteri (fun i (c, status) ->
          if i > 0 then Buffer.add_char b ',';
          Buffer.add_char b '{';
          json_string b "constant"; Buffer.add_char b ':';
          json_string b (Names.Constant.to_string c);
          Buffer.add_char b ',';
          json_string b "status"; Buffer.add_char b ':';
          json_string b (match status with LibkeyObjects.Axiom -> "axiom" | LibkeyObjects.Proof -> "proof");
          Buffer.add_char b '}')
        r.LibkeyObjects.blinded;
      Buffer.add_char b ']');
  field "foreign_opaque_libraries" (fun () ->
      Buffer.add_char b '[';
      List.iteri (fun i dp ->
          if i > 0 then Buffer.add_char b ',';
          json_string b (Names.DirPath.to_string dp))
        (Names.DirPath.Set.elements r.LibkeyObjects.foreign_opaque_libraries);
      Buffer.add_char b ']');
  Buffer.add_char b '}';
  Buffer.contents b

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
      let kind, lhex = check_kind (read f) in Printf.printf "%s %s\n" kind lhex
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
    | "--axiom-report-json" -> print_endline (axiom_report_json (read f))
    | _ -> usage ()
    end
  | _ -> usage ()
