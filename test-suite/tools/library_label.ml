(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Test oracle of the location-free library label (vernac/libkeyObjects.ml).
   - [--stored FILE.vo]: the digest the file stores for its library segment,
     in hex, as its dependents record it.
   - [--check FILE.vo]: "label" when that digest is the label recomputed from
     the segment's content, "md5" when it is the MD5 of the segment's bytes
     (a library with no label), "other" otherwise; then the stored digest.
   - [--attempts FILE.vo]: the attempted-resolution records (Attempts).
   Every object kind of rocq's own plugins is linked in (-linkall), so the
   kinds a library uses are registered as they are in [rocq compile]. *)

type library_disk = {
  md_compiled : Safe_typing.compiled_library;
  md_syntax_objects : Declaremods.library_objects;
  md_objects : Declaremods.library_objects;
}

let library_seg : library_disk ObjFile.id = ObjFile.make_id "library"

let hex s =
  String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))

let read_library file =
  let ch = ObjFile.open_in ~file in
  let md, digest = ObjFile.marshal_in_segment ch ~segment:library_seg in
  let seg = ObjFile.get_segment ch ~segment:library_seg in
  ObjFile.close_in ch;
  md, digest, seg

let segment_md5 file (seg : _ ObjFile.segment) =
  In_channel.with_open_bin file (fun ic ->
      In_channel.seek ic seg.pos;
      Digest.channel ic (Int64.to_int seg.len))

let () =
  match List.tl (Array.to_list Sys.argv) with
  | ["--stored"; f] -> let _, d, _ = read_library f in print_endline (hex d)
  | ["--check"; f] ->
    let md, d, seg = read_library f in
    let label = LibkeyObjects.label ~compiled:md.md_compiled ~syntax:md.md_syntax_objects
        ~objects:md.md_objects in
    let kind =
      if Option.equal String.equal label (Some d) then "label"
      else if String.equal (segment_md5 f seg) d then "md5"
      else "other"
    in
    Printf.printf "%s %s\n" kind (hex d)
  | ["--attempts"; f] ->
    let md, _, _ = read_library f in
    (match Attempts.find md.md_objects with
     | None -> print_endline "no attempts"
     | Some t -> List.iter print_endline (Attempts.describe t))
  | _ ->
    prerr_endline "usage: library_label (--stored | --check | --attempts) FILE.vo"; exit 2
