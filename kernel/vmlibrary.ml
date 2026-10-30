(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vmemitcodes

exception Faulty of string

(* TODO: share with Library *)

module Delayed :
sig

type 'a t
val make : file:string -> pos:int64 -> digest:Digest.t -> 'a t
val return : 'a -> 'a t
val eval : 'a t -> 'a

end =
struct

type 'a delayed = {
  del_file : string;
  del_off : int64;
  del_digest : Digest.t;
}

type 'a node = ToFetch of 'a delayed | Fetched of 'a

type 'a t = 'a node ref

let make ~file ~pos ~digest =
  ref (ToFetch { del_file = file; del_off = pos; del_digest = digest })

(** Fetching a table of opaque terms at position [pos] in file [f],
    expecting to find first a copy of [digest]. *)

let fetch_delayed del =
  let { del_digest = digest; del_file = f; del_off = pos; } = del in
  let ch = open_in_bin f in
  let obj, digest' =
    try
      let () = LargeFile.seek_in ch pos in
      let obj = System.marshal_in f ch in
      let digest' = Digest.input ch in
      obj, digest'
    with e -> close_in ch; raise e
  in
  close_in ch;
  if not (String.equal digest digest') then raise (Faulty f);
  obj

let eval r = match !r with
| Fetched v -> v
| ToFetch del ->
  let v = fetch_delayed del in
  let () = r := Fetched v in
  v

let return v = ref (Fetched v)

end

module VmTable =
struct

type t = {
  table_len : int;
  table_dir : DirPath.t;
  table_val : to_patch Int.Map.t;
}

type index = DirPath.t * int

let empty = {
  table_len = 0;
  table_dir = DirPath.dummy;
  table_val = Int.Map.empty;
}

let set_path dp tab =
  let () = assert (DirPath.equal tab.table_dir DirPath.dummy) in
  { tab with table_dir = dp }

let create code tab =
  let id = tab.table_len in
  let dp = tab.table_dir in
  let () = assert (not @@ DirPath.equal dp DirPath.dummy) in
  let table_val = Int.Map.add id code tab.table_val in
  let ntab = { table_dir = dp; table_len = id + 1; table_val } in
  ntab, (dp, id)

end

type compiled_library = {
  lib_dp : DirPath.t;
  lib_data : to_patch array;
}

type on_disk = DirPath.t * compiled_library Delayed.t

let inject lib =
  (lib.lib_dp, Delayed.return lib)

type t = {
  local : VmTable.t;
  foreign : compiled_library Delayed.t DirPath.Map.t;
}

type index = VmTable.index

type indirect_code = VmTable.index pbody_code

let empty = {
  local = VmTable.empty;
  foreign = DirPath.Map.empty;
}

let set_path dp lib =
  let local = VmTable.set_path dp lib.local in
  { lib with local }

let add code lib =
  let tab, idx = VmTable.create code lib.local in
  let lib = { lib with local = tab } in
  lib, idx

let segment_name = "vmlibrary"

let vm_segment : compiled_library ObjFile.id = ObjFile.make_id segment_name

(* Format of the vmlibrary segment.

   The segment holds the VM bytecode a library file carries: a marshalled
   [compiled_library], that is, emitted instruction strings together with the
   relocation data that patches them. Those bytes mean nothing on their own. An
   instruction is a word the C interpreter of the READING process dispatches on,
   so a process that does not have the opcodes the writer emitted jumps where
   its own table sends that word, and dies with no message: a library written by
   a Rocq whose VM has instructions this one lacks made the reader dump core
   (SIGABRT, dispatch://BET-241).

   The segment therefore starts with its own format version, a 32-bit big-endian
   word (the integer form the rest of the container uses, lib/objFile.ml),
   written before the marshalled table and read before anything in the segment is
   unmarshalled. A reader that finds a version it does not know refuses the file,
   naming the library and both versions.

   Raise [format_version] whenever what the segment stores changes: a new or
   renumbered opcode in the emitted code, a change of the marshalled types, or a
   change in what a reader must do with them. Nothing ties it to the opcode
   table, so a change that leaves it alone brings the crash back for the readers
   this check is for. It is the version of this segment alone, not of the file:
   the other segments stay readable, so a .vo whose vmlibrary a reader refuses
   is named rather than misread. *)
let format_version = 1

(* The version word, as [output_binary_int] writes it. A file written before
   there was one starts with the marshaller's magic instead, which is negative,
   so no value this reader can see is mistaken for a version. *)
let segment_header_bytes = 4

let format_mismatch dp ~file ~found =
  let found =
    if found > 0 then
      Pp.(str "is in vmlibrary format version " ++ int found)
    else
      Pp.(str "carries no vmlibrary format version, so it was written before \
               this check existed")
  in
  CErrors.user_err Pp.(str "The VM bytecode of library " ++ DirPath.print dp ++
    str " (file " ++ str file ++ str ") " ++ found ++
    str ", but this process reads vmlibrary format version " ++
    int format_version ++ str ". Rebuild that library with this Rocq.")

let save ch lib =
  let oc, finish = ObjFile.marshal_out_binary ch ~segment:vm_segment in
  let () = output_binary_int oc format_version in
  let () = Marshal.to_channel oc lib [] in
  finish ()

let load dp ~file ch =
  let found = ObjFile.input_segment_int ch ~segment:vm_segment in
  let () =
    if not (Int.equal found format_version) then format_mismatch dp ~file ~found
  in
  let seg = ObjFile.get_segment ch ~segment:vm_segment in
  (* The marshalled table starts after the version word. *)
  let pos = Int64.add seg.ObjFile.pos (Int64.of_int segment_header_bytes) in
  (dp, Delayed.make ~file ~pos ~digest:seg.ObjFile.hash : on_disk)

let link (dp, m) libs =
  let () = assert (not @@ DirPath.Map.mem dp libs.foreign) in
  { libs with foreign = DirPath.Map.add dp m libs.foreign }

let missing_index dp i =
  CErrors.anomaly Pp.(str "Missing VM index " ++ int i ++
    str " in library " ++ DirPath.print dp)

let resolve (dp, i) libs =
  if DirPath.equal dp libs.local.VmTable.table_dir then
    match Int.Map.find i libs.local.VmTable.table_val with
    | v -> v
    | exception Not_found -> missing_index dp i
  else match DirPath.Map.find dp libs.foreign with
  | tab ->
    let tab = Delayed.eval tab in
    tab.lib_data.(i)
  | exception Not_found ->
    CErrors.anomaly Pp.(str "Missing VM table for library " ++
      DirPath.print dp)

let export lib =
  let local = lib.local in
  let init i = Int.Map.find i local.VmTable.table_val in
  let data = Array.init local.VmTable.table_len init in
  { lib_dp = local.VmTable.table_dir; lib_data = data }
