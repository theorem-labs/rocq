(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module R = Proof_record

type source =
  | Record_file of string
  | Record_dir of string

type options = {
  o_source : source;
  o_peak_limit_kb : int option;
  o_digest : string option;  (** the record's SHA-256, from the registration's manifest *)
}

let options : options option ref = ref None

let configure ~source ~peak_limit_kb ~digest =
  options := Some { o_source = source; o_peak_limit_kb = peak_limit_kb; o_digest = digest }

let configured () = !options <> None

(* Where this library's record is. A file source is the record itself; a
   directory holds one record per library. Three places are tried: the
   library's dotted logical name, that name with its dots turned into
   slashes, and the path of the [.vo] this compile writes, relative to the
   working directory. The last is the layout of a registration tree, and
   of the engine's per-file staging. *)
let record_of_vo = ref None

let set_vo_path vo = record_of_vo := Some (Filename.remove_extension vo ^ ".proof-record.jsonl")

let record_path ~library = function
  | Record_file f -> Some f
  | Record_dir dir ->
    let places =
      [ library ^ ".proof-record.jsonl";
        String.concat Filename.dir_sep (String.split_on_char '.' library) ^ ".proof-record.jsonl" ]
      @ (match !record_of_vo with
          | Some p when Filename.is_relative p
                        && not (List.mem Filename.parent_dir_name (String.split_on_char '/' p)) -> [ p ]
          | Some _ | None -> [])
    in
    List.find_opt Sys.file_exists (List.map (Filename.concat dir) places)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(* A compile that ran under a limit which can end an allocation before the
   cgroup kill is not replayed, in either direction: under such a limit a
   proof can fail where the other run's did not, and a stored term would
   hide it (BET-84 spec, "When a stored term is used"). A value that could
   not be read ("unknown", a sandbox that masks /proc/sys) refuses too: a
   guard that cannot see is not a guard (review P3Deep F6). *)
let overcommit_refuses v = v <> "0" && v <> "1"

let limits_refusal (h : R.header) =
  if h.R.rlimit_as <> "unlimited" || h.R.rlimit_data <> "unlimited" then Some "rlimit"
  else if overcommit_refuses h.R.overcommit_memory then Some "overcommit"
  else None

let own_limits_refusal () =
  if Proof_limits.rlimit "Max address space" <> "unlimited"
     || Proof_limits.rlimit "Max data size" <> "unlimited"
  then Some "rlimit"
  else if overcommit_refuses (Proof_limits.overcommit_memory ()) then Some "overcommit"
  else None

(* The record is a TRUSTED input, at the same tier as the binary: its
   stored terms are read back with [Marshal.from_string], which is not
   memory-safe on chosen bytes, and a stored term's declared type comes
   from it. So the record is used only when it is bound to this compile
   (reviews P3Deep F1, P3Bugs):
   - its bytes hash (SHA-256) to an expected digest, which is mandatory:
     [-proof-replay-digest], which the grading engine takes from the
     registration's root-owned manifest, or with [-proof-replay-dir] a
     [<record>.sha256] file beside each record, as unwritable as it, in
     directories as unwritable as it;
   - nobody but its owner can write it, and the compiling user cannot
     write it at all: write permission is what would let a principal that
     runs as that user replace a record between the hash and the read. For
     root, which [access] always lets write, the mode bits decide;
   - its header names the library this compile builds, and it is a
     record format this binary writes ([tables_at_start]). *)
let writable_by_us path =
  match Unix.stat path with
  | exception Unix.Unix_error _ -> true
  | st ->
    st.Unix.st_perm land 0o022 <> 0
    || (if Unix.getuid () = 0 then st.Unix.st_perm land 0o222 <> 0
        else (try Unix.access path [ Unix.W_OK ]; true with Unix.Unix_error _ -> false))

(* The record's expected SHA-256 is MANDATORY (reviews P3Deep F1, P3Bugs):
   [-proof-replay FILE] requires [-proof-replay-digest]; with
   [-proof-replay-dir], each record's digest is read from
   [<record>.sha256] beside it, which must be as unwritable as the record.
   A record with no digest to check it against is refused. *)
let expected_digest path =
  match !options with
  | Some { o_digest = Some d; _ } -> Some d
  | Some { o_source = Record_dir _; _ } ->
    let side = path ^ ".sha256" in
    if not (Sys.file_exists side) || writable_by_us side then None
    else
      (match read_file side with
       | s when String.length s >= 64 -> Some (String.sub s 0 64)
       | _ -> None
       | exception (Sys_error _ | End_of_file) -> None)
  | Some { o_source = Record_file _; o_digest = None; _ } | None -> None

(* With [-proof-replay-dir] and no [-proof-replay-digest], the digest file
   is the authority, and it sits beside the record. A principal that can
   write a directory from [DIR] down to the record can put a new record and
   a new digest file there, each made read-only, and both pass the file
   tests. So [DIR] and each directory below it on the way to the record
   must be as unwritable as the record (reviewer round 2 of e560ab16e4,
   X4). With [-proof-replay-digest] the command line binds the bytes, and
   the directories decide nothing. [path] is the one {!record_path} built,
   [Filename.concat dir place] with [place] relative; any other path is
   refused. *)
let record_dirs_writable path =
  match !options with
  | Some { o_source = Record_dir dir; o_digest = None; _ } ->
    let prefix = Filename.concat dir "" in
    let n = String.length prefix in
    if String.length path < n || not (String.equal (String.sub path 0 n) prefix) then true
    else
      let rec below d = function
        | [] | [ _ ] -> false
        | c :: rest -> let d = Filename.concat d c in writable_by_us d || below d rest
      in
      writable_by_us dir
      || below dir (String.split_on_char '/' (String.sub path n (String.length path - n)))
  | Some _ | None -> false

let binding_refusal ~library ~path ~bytes (h : R.header) =
  match expected_digest path with
  | None -> Some "digest"
  | Some d when not (String.equal (String.lowercase_ascii d) (Proof_sha256.digest_hex bytes)) ->
    Some "digest"
  | Some _ ->
    if writable_by_us path || record_dirs_writable path then Some "writable"
    else if not (String.equal h.R.library library) then Some "library"
    else if not h.R.tables_at_start then Some "format"
    else None

(* A file whose registration needed more memory than the share this grade
   can give one compile runs without replay: all the build's jobs share one
   cgroup, so stock's own memory failures depend on what else runs. *)
let peak_refusal opts (t : R.trailer) =
  match opts.o_peak_limit_kb with
  | Some limit when t.R.peak_rss_kb > limit -> Some "memory"
  | _ -> None

(* A record another toolchain wrote is refused for the whole file, before
   any proof of it is declared: an object built by one Rocq can fail coqchk
   under another (the guard fix of 2026-10-25 made two let-based shapes
   fail that passed before it). The per-proof key holds the same items, so
   this is a second layer that names the reason once, in the summary.

   The load order is compared by the libraries' names, as the key compares
   it: a required library the agent edited has another digest, and a file
   that requires it is exactly the file replay exists for. Its contents
   reach a proof only through the reads, which are checked one by one. The
   warnings are not compared here: they are a per-proof key item, and a
   file can change them with [Set Warnings].

   A digest of the binary or of a plugin's files that could not be read is
   {!R.unknown_digest} in every compile that meets it, so two of them are
   equal whatever the files were. A record must not match through them:
   its stored terms would be unmarshalled as this binary's types. So a
   toolchain with such a digest is refused too (reviewer round 2 of
   e560ab16e4, X5). *)
let toolchain_refusal ~(now : R.toolchain) (h : R.header) =
  let r = h.R.toolchain in
  if r.R.binary <> now.R.binary || r.R.plugins <> now.R.plugins
     || List.map fst r.R.load_order <> List.map fst now.R.load_order
     || r.R.safe_deps <> now.R.safe_deps || r.R.stack_limit <> now.R.stack_limit
     || R.toolchain_unknown now <> None
  then Some "toolchain"
  else None

type loaded = {
  index : (string, R.proof) Hashtbl.t;
  registered_object : string * string option;
}

(* A [-proof-replay-dir] with no record for this library is refused as
   ["no_record"]: a file the registration never saw, such as one the
   author added. A record that is named or found but cannot be read (a
   [-proof-replay FILE] that does not exist or that this user cannot
   open, a record of [-proof-replay-dir] removed or cut between
   [record_path] and this read) is refused as one that does not parse,
   ["bad_record"] (deep review of 079bc4cb71, DR-1). Either way the file
   runs its tactics. Only the read's own failures are caught. *)
let load ~library ~toolchain =
  match !options with
  | None -> None
  | Some opts ->
    Some
      (match record_path ~library opts.o_source with
       | None -> Error "no_record"
       | Some path ->
         match read_file path with
         | exception (Sys_error _ | End_of_file) -> Error "bad_record"
         | bytes ->
           match R.parse_string bytes with
           | exception _ -> Error "bad_record"
           | file ->
             let refusal =
               match binding_refusal ~library ~path ~bytes file.R.header with
               | Some r -> Some r
               | None ->
               match toolchain_refusal ~now:(toolchain ()) file.R.header with
               | Some r -> Some r
               | None ->
               match limits_refusal file.R.header with
               | Some r -> Some r
               | None ->
                 (match own_limits_refusal () with
                  | Some r -> Some r
                  | None -> peak_refusal opts file.R.trailer)
             in
             match refusal with
             | Some r -> Error r
             | None ->
               let index = Hashtbl.create 256 in
               List.iter (fun (p : R.proof) -> Hashtbl.replace index p.R.name p) file.R.proofs;
               (* The registration's object sits beside its record, under the
                  same name: a registration tree, and a directory of records
                  that a registration published with their objects. *)
               let base =
                 if Filename.check_suffix path ".proof-record.jsonl" then
                   Filename.chop_suffix path ".proof-record.jsonl"
                 else Filename.remove_extension path
               in
               Ok { index; registered_object = (base ^ ".vo", file.R.trailer.R.vo_opaques) })
