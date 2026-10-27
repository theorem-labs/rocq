(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The directory of Print Assumptions entries that the processes of one build
    share: the files, their claims and the key of an object. What the entries
    mean, and why reusing one cannot change an answer, is in
    {!Assumptions}. *)

open Names


(** The directory, from [ROCQ_ASSUMPTIONS_SHARED_DIR].

    Its precondition, besides holding only what the processes of one build
    over one set of library files wrote: THE LIBRARY FILES THE BUILD READS
    ARE IMMUTABLE FOR THE LENGTH OF THE BUILD. A key covers the digests a
    file recorded when it was read, not that the file is still there and
    whole. A library file damaged after a process required it therefore
    answers from the entry written while its proofs could be read, where a
    process without the directory reads the damaged file and reports the
    lemma itself as an axiom. The same mutable file already decides the
    answer without any directory: a library replaced by another build of
    itself before the Require makes the query print the other build's
    axioms. Give a build files nothing it runs can write. *)
let dir = match Sys.getenv_opt "ROCQ_ASSUMPTIONS_SHARED_DIR" with
  | Some d when not (String.equal d "") -> Some d
  | _ -> None

(* ROCQ_DEBUG_ASSUMPTIONS_SHARED=1: one line per query, on standard error,
   like ROCQ_DEBUG_ASSUMPTIONS_MEMO. *)
let debug = Sys.getenv_opt "ROCQ_DEBUG_ASSUMPTIONS_SHARED" = Some "1"

let usable = ref (Option.has_some dir)

let disable what e =
  if !usable && debug then
    Printf.eprintf "[assumptions-shared] off after %s: %s\n%!" what (Printexc.to_string e);
  usable := false

let path sub = Filename.concat (Option.get dir) sub

(** References compared by user and canonical name: the identity of an
    object for [find_entry]. *)
module Exact = struct
  type t = GlobRef.t
  let compare a b =
    let c = GlobRef.UserOrd.compare a b in
    if c <> 0 then c else GlobRef.CanOrd.compare a b
end
module EMap = Map.Make (Exact)

(** What a walk of one object found: a constant or variable without a body
    and the references of its type, one with a body and its references, an
    inductive block and its references, or a walk that raised. *)
type kind = No_body | Body | Block | Failed

(** One entry, as written to the directory. *)
type found = { f_kind : kind; f_replayable : bool; f_refs : GlobRef.t list }

(** One entry, as written to the directory. *)
type record = { r_key : string; r_found : found }

(** The first line of every entry file. It names the binary that wrote the
    entry, not only its version: a reader reads the entry with [Marshal],
    so an entry whose [record] has another shape is bytes read at the wrong
    type rather than a miss, and two builds of one Rocq version can differ
    in that shape. The file of the running binary stands for it: its device,
    inode, size and modification time, which an installed Rocq keeps and a
    rebuild changes. *)
let magic =
  let build = match Unix.stat Sys.executable_name with
    | st ->
      Printf.sprintf "%d:%d:%d:%.0f"
        st.Unix.st_dev st.Unix.st_ino st.Unix.st_size st.Unix.st_mtime
    | exception Unix.Unix_error _ -> Sys.executable_name
  in
  Printf.sprintf "rocq-assumptions-shared 2 %s %s %d %s\n"
    Coq_config.version Coq_config.caml_version Sys.word_size build

let magic_length = String.length magic

(* For each key, two files in one of 256 directories (so that the processes
   creating files seldom wait for one another): the claim, which the first
   process to create it owns, and the entry: [magic], the MD5 of the
   payload, the payload (the marshaled record). The entry is written under
   a name of the writer's own and renamed into place, so a reader finds
   nothing or the whole file; a reader also takes it only when its digest
   matches. *)
let out_buffer = ref (Bytes.create 65536)

(* The entry file of [record], in [!out_buffer], and its length. Built in
   place: an entry is a few kilobytes, which the major heap would otherwise
   take several times over at each write. *)
let rec contents record =
  let b = !out_buffer in
  let start = magic_length + 16 in
  match Marshal.to_buffer b start (Bytes.length b - start) record [] with
  | n ->
    Bytes.blit_string magic 0 b 0 magic_length;
    Bytes.blit_string (Digest.subbytes b start n) 0 b magic_length 16;
    start + n
  | exception Failure _ ->
    out_buffer := Bytes.create (2 * Bytes.length b);
    contents record

let rec write_all fd b off len =
  if len > 0 then
    let k = Unix.write fd b off len in
    write_all fd b (off + k) (len - k)

let mkdir d = try Unix.mkdir d 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()

let file_of key =
  let h = Digest.to_hex (Digest.string key) in
  Filename.concat (Filename.concat (path "entries") (String.sub h 0 2)) h

let claim_of key = file_of key ^ ".claim"

(** Entries this process read or wrote, by key. Cleared with the entries of
    the query cache ([forget], called from [sync_memo] through
    [forget_shared], since this module comes after it), so that a process
    that shares keeps no more of them than one that does not: what it drops
    it reads again from the directory. *)
let index : (string, found) Hashtbl.t = Hashtbl.create 1024

let forget () = Hashtbl.reset index

type claim =
  | Mine of Unix.file_descr
  (** this process holds the claim, open: locked, unless the system
      refused the lock, which only lets another process walk the object
      too *)
  | Taken  (** another process holds it *)
  | Off  (** sharing is off: the process walks every object itself *)

let lock fd = try Unix.lockf fd Unix.F_TLOCK 0; true with Unix.Unix_error _ -> false

(** Claims [key]: the first process to create its claim gets it. *)
let claim key =
  if not !usable then Off
  else
    match Unix.openfile (claim_of key) [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL; Unix.O_CLOEXEC] 0o600 with
    | fd -> ignore (lock fd : bool); Mine fd
    | exception Unix.Unix_error (Unix.EEXIST, _, _) -> Taken
    | exception (Unix.Unix_error _ as e) -> disable "a claim" e; Off

(** The claim of [key] when the process that held it ended without writing
    the entry, so that its lock is free; [Taken] while a process holds it. A
    lock taken in the moment between the claimant's creating the claim and
    locking it makes two processes walk the object, which write equal
    entries. *)
let take_over key =
  if not !usable then Off
  else
    match Unix.openfile (claim_of key) [Unix.O_WRONLY; Unix.O_CLOEXEC] 0 with
    | exception (Unix.Unix_error _ as e) -> disable "a claim" e; Off
    | fd ->
      if lock fd then Mine fd
      else begin (try Unix.close fd with Unix.Unix_error _ -> ()); Taken end

(** Keeps the entry of [key], and writes it to the directory when this
    process holds the claim, which it then releases. *)
let publish claim key (found : found) =
  Hashtbl.replace index key found;
  match claim with
  | Taken | Off -> ()
  | Mine claim_fd ->
    try
      Fun.protect ~finally:(fun () -> Unix.close claim_fd) (fun () ->
          if !usable then begin
            let file = file_of key in
            let tmp = Printf.sprintf "%s.%d.tmp" file (Unix.getpid ()) in
            let n = contents { r_key = key; r_found = found } in
            let fd = Unix.openfile tmp [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC; Unix.O_CLOEXEC] 0o600 in
            Fun.protect ~finally:(fun () -> Unix.close fd) (fun () -> write_all fd !out_buffer 0 n);
            (* No fsync before the rename, on purpose. The rename alone makes
               the entry appear whole or not at all to the other processes of
               the build, which share this host's page cache. An fsync guards
               only against a crash or a power loss, after which nothing
               reads the directory: it serves one build and is made fresh for
               the next. A file a crash did leave truncated or stale fails the
               digest check in [read] and counts as a miss. An fsync costs
               about 1.7 ms per entry (against 23 us without), 12-24 s for a
               file that writes 7,000-14,000 entries. *)
            Unix.rename tmp file
          end)
    with (Unix.Unix_error _ | Fun.Finally_raised _) as e -> disable "a write" e

(** Releases the claim of an object whose walk raised. *)
let abandon = function
  | Mine fd -> (try Unix.close fd with Unix.Unix_error _ -> ())
  | Taken | Off -> ()

let buffer = ref (Bytes.create 65536)

(* The entry of [key] in the directory, when its digest matches: the bytes
   are checked before [Marshal] reads them. *)
let read key =
  match Unix.openfile (file_of key) [Unix.O_RDONLY; Unix.O_CLOEXEC] 0 with
  | exception Unix.Unix_error (Unix.ENOENT, _, _) -> None
  | fd ->
    let n = Fun.protect ~finally:(fun () -> Unix.close fd) (fun () ->
        let n = (Unix.fstat fd).Unix.st_size in
        if Bytes.length !buffer < n then buffer := Bytes.create n;
        let rec fill k =
          if k >= n then k
          else match Unix.read fd !buffer k (n - k) with
            | 0 -> k
            | r -> fill (k + r)
        in
        fill 0)
    in
    let b = !buffer in
    let start = magic_length + 16 in
    if n < start || not (String.equal (Bytes.sub_string b 0 magic_length) magic)
       || not (String.equal (Bytes.sub_string b magic_length 16) (Digest.subbytes b start (n - start)))
    then None
    else
      let r : record = Marshal.from_bytes b start in
      if not (String.equal r.r_key key) then None
      else begin
        Hashtbl.replace index key r.r_found;
        Some r.r_found
      end

(** Where the entry of [key] came from, for the counters the debug line
    reports and the test reads: the directory, or this process's own index
    (an entry it wrote, or read before). *)
type source = From_directory | From_index

(** The entry of [key], read once from the directory. A file that is not a
    whole entry of [key] (another build, a damaged file, a key whose MD5
    collides) counts as absent. *)
let find key =
  match Hashtbl.find_opt index key with
  | Some f -> Some (From_index, f)
  | None ->
    if not !usable then None
    else
      match read key with
      | Some f -> Some (From_directory, f)
      | None -> None
      | exception ((Unix.Unix_error _ | Sys_error _ | Failure _ | Invalid_argument _
                   | End_of_file | Fun.Finally_raised _) as e) ->
        disable "a read" e; None

let started = ref false

let start () =
  if !usable && not !started then
    try
      mkdir (path "entries");
      for i = 0 to 255 do mkdir (Filename.concat (path "entries") (Printf.sprintf "%02x" i)) done;
      started := true
    with (Unix.Unix_error _ | Sys_error _) as e -> disable "setting up the directory" e

let add_name b id =
  let s = Id.to_string id in
  Buffer.add_string b (string_of_int (String.length s));
  Buffer.add_char b ':';
  Buffer.add_string b s

let rec add_modpath b = function
  | ModPath.MPfile dp -> Buffer.add_char b 'F'; List.iter (add_name b) (DirPath.repr dp); Buffer.add_char b ';'
  | ModPath.MPbound _ -> raise Exit
  | ModPath.MPdot (mp, l) -> add_modpath b mp; Buffer.add_char b '.'; add_name b l

let add_kername b kn =
  let mp, l = KerName.repr kn in
  add_modpath b mp;
  Buffer.add_char b '/';
  add_name b l

let rec library = function
  | ModPath.MPfile dp -> dp
  | ModPath.MPbound _ -> raise Exit
  | ModPath.MPdot (mp, _) -> library mp

(** The key of an object, or of the inductive block of an inductive or
    constructor: its user and canonical names, and the
    [Library.content_digests] of the libraries they belong to; [None] for an
    object that is not shared: a section variable, an object under a functor
    parameter, or one of a library that is not loaded. *)
let key digests obj =
  let of_names tag user canonical =
    let digest kn = match digests (library (KerName.modpath kn)) with
      | Some d -> d
      | None -> raise Exit
    in
    try
      let b = Buffer.create 128 in
      Buffer.add_char b tag;
      add_kername b user;
      Buffer.add_char b '|';
      add_kername b canonical;
      Buffer.add_char b '|';
      Buffer.add_string b (digest user);
      Buffer.add_string b (digest canonical);
      Some (Buffer.contents b)
    with Exit -> None
  in
  match obj with
  | GlobRef.VarRef _ -> None
  | GlobRef.ConstRef c -> of_names 'C' (Constant.user c) (Constant.canonical c)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    of_names 'I' (MutInd.user mind) (MutInd.canonical mind)
