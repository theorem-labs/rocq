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
open System

let magic_number = 0x436F7121l (* "Coq!" *)

let error_corrupted file s =
  CErrors.user_err (str file ++ str ": " ++ str s ++ str ". Try to rebuild it.")

let open_trapping_failure name =
  try open_out_bin name
  with e when CErrors.noncritical e ->
    CErrors.user_err (str "Can't open " ++ str name ++ spc() ++ str "(" ++ CErrors.print e ++ str ").")

(*

int32: big-endian, 4 bytes
int64: big-endian, 8 bytes

-- string --
int32 | length of the next field
data  |

-- segment summary --
string | name
int64  | absolute position
int64  | length (without hash)
hash   | MD5 (16 bytes)

-- segment --
...  | binary data
hash | MD5 (16 bytes)

-- summary --
int32 | number of segment summaries
s1    |
...   | segment summaries
sn    |

-- vo --
int32   | magic number
int32   | Coq version
int64   | absolute position of the summary
...     | segments
summary |

*)

type 'a segment = {
  name : string;
  pos : int64;
  len : int64;
  hash : Digest.t;
}

type in_handle = {
  in_filename : string;
  in_channel : in_channel;
  in_segments : Obj.t segment CString.Map.t;
}

type out_handle = {
  out_filename : string;
  out_channel : out_channel;
  mutable out_segments : Obj.t segment CString.Map.t;
}

type 'a id = { id : string }

let make_id id = { id }

let input_segment_summary ch =
  let nlen = input_int32 ch in
  let name = really_input_string ch (Int32.to_int nlen) in
  let pos = input_int64 ch in
  let len = input_int64 ch in
  let hash = Digest.input ch in
  { name; pos; len; hash }

let output_segment_summary ch seg =
  let nlen = Int32.of_int (String.length seg.name) in
  let () = output_int32 ch nlen in
  let () = output_string ch seg.name in
  let () = output_int64 ch seg.pos in
  let () = output_int64 ch seg.len in
  let () = Digest.output ch seg.hash in
  ()

let rec input_segment_summaries ch n accu =
  if Int32.equal n 0l then accu
  else
    let s = input_segment_summary ch in
    let accu = CString.Map.add s.name s accu in
    input_segment_summaries ch (Int32.pred n) accu

let marshal_in_segment (type a) h ~segment : a * Digest.t =
  let { in_channel = ch } = h in
  let s = CString.Map.find segment.id h.in_segments in
  let () = LargeFile.seek_in ch s.pos in
  let (v : a) = marshal_in h.in_filename ch in
  let () = assert (Int64.equal (LargeFile.pos_in ch) (Int64.add s.pos s.len)) in
  let h = Digest.input ch in
  let () = assert (String.equal h s.hash) in
  (v, s.hash)

let marshal_out_segment h ~segment v =
  let { out_channel = ch } = h in
  let () = assert (not (CString.Map.mem segment.id h.out_segments)) in
  let pos = LargeFile.pos_out ch in
  let () = Marshal.to_channel ch v [] in
  let () = flush ch in
  let pos' = LargeFile.pos_out ch in
  let len = Int64.sub pos' pos in
  let hash =
    let in_ch = open_in_bin h.out_filename in
    let () = LargeFile.seek_in in_ch pos in
    let digest = Digest.channel in_ch (Int64.to_int len) in
    let () = close_in in_ch in
    digest
  in
  let () = Digest.output ch hash in
  let s = { name = segment.id; pos; len; hash } in
  let () = h.out_segments <- CString.Map.add segment.id s h.out_segments in
  ()

let marshal_out_binary h ~segment =
  let { out_channel = ch } = h in
  let () = assert (not (CString.Map.mem segment.id h.out_segments)) in
  let pos = LargeFile.pos_out ch in
  let finish () =
    let () = flush ch in
    let pos' = LargeFile.pos_out ch in
    let len = Int64.sub pos' pos in
    let hash =
      let in_ch = open_in_bin h.out_filename in
      let () = LargeFile.seek_in in_ch pos in
      let digest = Digest.channel in_ch (Int64.to_int len) in
      let () = close_in in_ch in
      digest
    in
    let () = Digest.output ch hash in
    let s = { name = segment.id; pos; len; hash } in
    h.out_segments <- CString.Map.add segment.id s h.out_segments
  in
  ch, finish

let open_in ~file =
  try
    let ch = open_in_bin file in
    let magic = input_int32 ch in
    let version = input_int32 ch in
    let () =
      if not (Int32.equal magic magic_number) then
        let e = { filename = file; actual = magic; expected = magic_number } in
        raise (Bad_magic_number e)
    in
    let () =
      let expected = Coq_config.vo_version in
      if not (Int32.equal version expected) then
        let e = { filename = file; actual = version; expected } in
        raise (Bad_version_number e)
    in
    let summary_pos = input_int64 ch in
    let () = LargeFile.seek_in ch summary_pos in
    let nsum = input_int32 ch in
    let seg = input_segment_summaries ch nsum CString.Map.empty in
    { in_filename = file; in_channel = ch; in_segments = seg }
  with
  | End_of_file -> error_corrupted file "premature end of file"
  | Failure s | Sys_error s -> error_corrupted file s

let close_in ch =
  close_in ch.in_channel

let get_segment (type a) ch ~(segment : a id) : a segment =
  (CString.Map.find segment.id ch.in_segments :> a segment)

let segments ch = ch.in_segments

let open_out ~file =
  let ch = open_trapping_failure file in
  let () = output_int32 ch magic_number in
  let () = output_int32 ch Coq_config.vo_version in
  let () = output_int64 ch 0L (* placeholder *) in
  { out_channel = ch; out_segments = CString.Map.empty; out_filename = file }

let close_out { out_channel = ch; out_segments = seg } =
  let () = flush ch in
  let pos = LargeFile.pos_out ch in
  (* Write the segment summary *)
  let () = output_int32 ch (Int32.of_int (CString.Map.cardinal seg)) in
  let iter _ s = output_segment_summary ch s in
  let () = CString.Map.iter iter seg in
  (* Overwrite the position place holder *)
  let () = LargeFile.seek_out ch 8L in
  let () = output_int64 ch pos in
  let () = flush ch in
  close_out ch

(* perf-nametab-cache v2 (ROCQ-INTERNALS.md Section 17/19 follow-up): attach
   a new segment to a .vo ALREADY WRITTEN AND CLOSED by [close_out], from a
   process other than (and strictly after) the one that wrote it, without
   reading, re-marshaling, or moving a single byte of any existing segment.

   Copies the file's existing bytes up to the end of its last segment's
   (data, hash) verbatim into a fresh temporary file (never touches the
   original until the final rename), appends the new segment there with
   the exact same marshal+hash discipline [marshal_out_segment] uses, and
   writes a regenerated segment table (every old entry byte-for-byte
   unchanged, plus the new one) and header pointer, then atomically renames
   the temporary file over the original. If anything fails before the
   rename, the original file is untouched. *)
let append_segment (type a) ~file ~(segment : a id) (v : a) =
  (* Red-team finding (NameCacheV2.WateryLadybug): the segment table and
     the byte copy below must come from the SAME open file descriptor, not
     two independent [open_in] calls -- two separate opens leave a TOCTOU
     window a concurrent recompile of this exact library could land in
     (the table read from the first open no longer matching the bytes the
     second open copies). One handle, read start to finish, closes that
     window: whatever [old_segs]/[old_end] describe is exactly what the
     byte copy below reads back, because it is the same underlying file
     descriptor's view, never re-opened in between. *)
  let h = open_in ~file in
  let old_segs = h.in_segments in
  let () =
    if CString.Map.mem segment.id old_segs then begin
      close_in h;
      CErrors.anomaly
        Pp.(str "ObjFile.append_segment: segment " ++ str segment.id
            ++ str " already present in " ++ str file)
    end
  in
  (* End of the last segment's (data, hash): recomputed from the table
     itself (not trusted from a single stored field) so a short/corrupt
     old file is caught here rather than silently truncating live bytes. *)
  let old_end =
    CString.Map.fold
      (fun _ s acc -> Int64.max acc (Int64.add s.pos (Int64.add s.len 16L)))
      old_segs 0L
  in
  let tmp = file ^ ".nametab-append.tmp" in
  let dst = open_trapping_failure tmp in
  let () =
    LargeFile.seek_in h.in_channel 0L;
    let buf = Bytes.create 65536 in
    let remaining = ref old_end in
    while Int64.compare !remaining 0L > 0 do
      let want = Int64.to_int (Int64.min !remaining 65536L) in
      let n = Stdlib.input h.in_channel buf 0 want in
      let () =
        if n = 0 then begin
          close_in h; Stdlib.close_out dst;
          CErrors.anomaly
            Pp.(str "ObjFile.append_segment: " ++ str file
                ++ str " is shorter than its own segment table claims")
        end
      in
      let () = Stdlib.output dst buf 0 n in
      remaining := Int64.sub !remaining (Int64.of_int n)
    done
  in
  let () = close_in h in
  let pos = LargeFile.pos_out dst in
  let () = assert (Int64.equal pos old_end) in
  let () = Marshal.to_channel dst v [] in
  let () = flush dst in
  let pos' = LargeFile.pos_out dst in
  let len = Int64.sub pos' pos in
  let hash =
    (* Same discipline as [marshal_out_segment]: hash the bytes back out of
       the file rather than the in-memory value, so [marshal_in_segment]'s
       own hash check reads back exactly what landed on disk. *)
    let in_ch = Stdlib.open_in_bin tmp in
    let () = LargeFile.seek_in in_ch pos in
    let digest = Digest.channel in_ch (Int64.to_int len) in
    let () = Stdlib.close_in in_ch in
    digest
  in
  let () = Digest.output dst hash in
  let new_seg = { name = segment.id; pos; len; hash } in
  let all_segs = CString.Map.add segment.id new_seg old_segs in
  let table_pos = LargeFile.pos_out dst in
  let () = output_int32 dst (Int32.of_int (CString.Map.cardinal all_segs)) in
  let () = CString.Map.iter (fun _ s -> output_segment_summary dst s) all_segs in
  let () = flush dst in
  let () = LargeFile.seek_out dst 8L in
  let () = output_int64 dst table_pos in
  let () = flush dst in
  let () = Stdlib.close_out dst in
  Sys.rename tmp file
