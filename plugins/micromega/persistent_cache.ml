(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(*  A persistent hashtable                                              *)
(*                                                                      *)
(*  Frédéric Besson (Inria Rennes) 2009-2014                            *)
(*                                                                      *)
(************************************************************************)

(** Last PR that requires the regeneration of caches.
    It is stored and checked after the Rocq magic number.
    Incompatible caches are thrown away.
*)
let pcache_version = 15584l

module type PHashtable = sig
  (* see documentation in [persistent_cache.mli] *)
  type 'a t
  type key

  val open_in : string -> 'a t
  val find : 'a t -> key -> 'a
  val add : 'a t -> key -> 'a -> unit
  val memo : string -> (key -> 'a) -> key -> 'a
  val memo_cond : string -> (key -> bool) -> (key -> 'a) -> key -> 'a
end

open Hashtbl
open System

(* BET-84 census row 23. A lookup returns what the cache file held when its
   table was opened, or what the prover computes. Its entries are read back
   from the file, and the plugin only appends to a valid file, so what the
   table loaded fixes every answer it gives. So a recorded proof reads, for
   each cache file its provers look up, what the table held at its opening.
   A replay that finds another value runs the tactics, which read the file
   as stock does. *)
type opened =
  | No_entry
  (* The table loaded no entry: its path is blocked (the grading engine makes
     it a directory), or the file is absent, empty or reset. Every lookup
     misses and the prover runs. *)
  | Entries of string
  (* The digest of the file's bytes. *)
  | Unhashed
  (* Entries, loaded while no record or replay was tracked
     ([Proof_recorder.tracking]), so no digest was taken. *)

(* The table of each memo function, by its file name, opened as the memo's
   first lookup opens it. *)
let caches : (string, (unit -> opened) list) Hashtbl.t = Hashtbl.create 4

let register_cache file opened =
  let others = Option.default [] (Hashtbl.find_opt caches file) in
  Hashtbl.replace caches file (opened :: others)

(* ONE value function, called by the record site and by the replay evaluator
   (dev/tools/census/replay_channels.py). [Unknown] for a file that no memo
   uses or two memos use (each one loads its own table), and for entries
   that no digest was taken of. *)
let recorded_micromega_cache file =
  match Hashtbl.find_opt caches file with
  | Some [opened] ->
    begin match opened () with
    | No_entry -> Proof_replay.Value None
    | Entries digest -> Proof_replay.Value (Some digest)
    | Unhashed -> Proof_replay.Unknown
    end
  | Some _ | None -> Proof_replay.Unknown

let () = Proof_replay.register_evaluator "micromega_cache" recorded_micromega_cache

let record_lookup file =
  if Proof_recorder.active () then
    Proof_recorder.read ~row:"23" ~channel:"micromega_cache" ~key:(fun () -> file)
      ~value:(fun () ->
          match recorded_micromega_cache file with
          | Proof_replay.Value v -> v
          | Proof_replay.Unknown ->
            Proof_recorder.ineligible ~reason:"micromega_cache" ~detail:file;
            None)

module PHashtable (Key : HashedType) : PHashtable with type key = Key.t = struct
  open Unix

  type key = Key.t

  module Table :
  sig
    type 'a t
    val empty : 'a t
    val add : int -> 'a -> 'a t -> 'a t
    val find : int -> 'a t -> 'a list
    val is_empty : 'a t -> bool
  end =
  struct
    type 'a t = 'a list Int.Map.t
    let empty = Int.Map.empty
    let add h pos tab =
      try Int.Map.modify h (fun _ l -> pos :: l) tab
      with Not_found -> Int.Map.add h [pos] tab

    let find h tab = Int.Map.find h tab
    let is_empty = Int.Map.is_empty
  end
  (* A mapping key hash -> file position *)

  type 'a data = { pos : int option ; mutable obj : (Key.t * 'a) option }

  type 'a t = {outch : out_channel; mutable htbl : 'a data Table.t; file : string;
               opened : opened (* BET-84: what the table loaded *) }

  let skip_blob ch =
    let hd = Bytes.create Marshal.header_size in
    let () = really_input ch hd 0 Marshal.header_size in
    let len = Marshal.data_size hd 0 in
    let pos = pos_in ch in
    seek_in ch (pos + len)

  let read_key_elem inch = match input_binary_int inch with
  | hash ->
    let pos = pos_in inch in
    let () = skip_blob inch in
    Some (hash, pos)
  | exception End_of_file -> None

  (**
    We used to only lock/unlock regions.
    Is-it more robust/portable to lock/unlock a fixed region e.g. [0;1]?
    In case of locking failure, the cache is not used.
**)

  type lock_kind = Read | Write

  let lock kd fd =
    let pos = lseek fd 0 SEEK_CUR in
    let success =
      try
        ignore (lseek fd 0 SEEK_SET);
        let lk = match kd with Read -> F_RLOCK | Write -> F_LOCK in
        lockf fd lk 1; true
      with Unix.Unix_error (_, _, _) -> false
    in
    ignore (lseek fd pos SEEK_SET);
    success

  let unlock fd =
    let pos = lseek fd 0 SEEK_CUR in
    let () =
      try
        ignore (lseek fd 0 SEEK_SET);
        lockf fd F_ULOCK 1
      with Unix.Unix_error (_, _, _) ->
        (* Here, this is really bad news --
           there is a pending lock which could cause a deadlock.
           Should it be an anomaly or produce a warning ?
        *)
        ignore (lseek fd pos SEEK_SET)
    in
    ()

  (* We make the assumption that an acquired lock can always be released *)

  let do_under_lock kd fd f =
    if lock kd fd then Some(Fun.protect f ~finally:(fun () -> unlock fd)) else None

  let fopen_in = open_in_bin

  let check_magic_number_and_version inch =
    try
      let magic = input_int32 inch in
      let version = input_int32 inch in
      magic = ObjFile.magic_number && version = pcache_version
    with End_of_file -> false

  (* BET-84: the bytes whose entries [xload] just loaded, read again under
     the same lock, so that no writer appends between the two. Only a
     compile that records or replays pays for this read. *)
  let opened_of inch table =
    if Table.is_empty table then No_entry
    else if not (Proof_recorder.tracking ()) then Unhashed
    else
      match (seek_in inch 0; Digest.channel inch (-1)) with
      | digest -> Entries (Digest.to_hex digest)
      | exception e when CErrors.noncritical e -> Unhashed

  let open_in (type a) f : a t =
    let flags = [O_RDONLY; O_CREAT] in
    let finch = openfile f flags 0o666 in
    let inch = in_channel_of_descr finch in
    let exception InvalidTableFormat  in
    let rec xload table =
      match read_key_elem inch with
      | None -> table
      | Some (hash, pos) -> xload (Table.add hash { pos =  Some pos; obj = None } table)
      | exception e when CErrors.noncritical e -> raise InvalidTableFormat
    in

    try
      (* Locking of the (whole) file while reading *)
      let loaded = do_under_lock Read finch (fun () ->
          let table = Table.empty in
          if check_magic_number_and_version inch
          then let table = xload table in (table, opened_of inch table)
          else raise InvalidTableFormat
        ) in
      let () = close_in_noerr inch in
      let outch = out_channel_of_descr (openfile f [O_WRONLY; O_APPEND; O_CREAT] 0o666) in
      let htbl, opened = Option.default (Table.empty, No_entry) loaded in
      { outch ; file = f; htbl; opened }
    with InvalidTableFormat ->
      let () = close_in_noerr inch in
      let flags = [O_WRONLY; O_TRUNC; O_APPEND; O_CREAT] in
      let out = openfile f flags 0o666 in
      let outch = out_channel_of_descr out in
      output_int32 outch ObjFile.magic_number;
      output_int32 outch pcache_version;
      {outch; htbl=Table.empty; file = f; opened = No_entry}

  let add t k e =
    let {outch} = t in
    let fd = descr_of_out_channel outch in
    let h = Key.hash k land 0x7FFFFFFF in
    let dump () =
      let () = output_binary_int outch h in
      let () = Marshal.to_channel outch (k, e) [] in
      let () = flush outch in
      ()
    in
    let  _ = do_under_lock Write fd dump in
    t.htbl <- Table.add h { pos=None; obj = Some (k, e) } t.htbl

  let find t k =
    let {outch; htbl = tbl} = t in
    let h = Key.hash k land 0x7FFFFFFF in
    let lpos = Table.find h tbl in
    (* First look for already live data *)
    let find data = match data.obj with
    | Some (k', v) -> if Key.equal k k' then Some v else None
    | None -> None
    in
    match CList.find_map find lpos with
    | Some res -> res
    | None ->
      (* Otherwise perform I/O and look at the disk cache *)
      let lpos = List.filter (fun data -> Option.is_empty data.obj) lpos in
      let () = if CList.is_empty lpos then raise Not_found in
      let ch = fopen_in t.file in
      let find data =
        match data.pos with
        | None -> None
        | Some pos ->
          let () = seek_in ch pos in
          match Marshal.from_channel ch with
          | (k', v) ->
            if Key.equal k k' then
              (* Store the data in memory *)
              let () = data.obj <- Some (k, v) in
              Some v
            else None
          | exception End_of_file | exception Failure _ -> None
      in
      let lookup () = CList.find_map find lpos in
      let res = do_under_lock Read (descr_of_in_channel ch) lookup in
      let () = close_in_noerr ch in
      match res with
      | Some (Some v) -> v
      | None | Some None -> raise Not_found

  (* The table [cache] names, opened at the first lookup. Replay finds it
     by that name (BET-84 census row 23). *)
  let lazy_table cache =
    let tbl = lazy (try Some (open_in cache) with e when CErrors.noncritical e -> None) in
    register_cache cache (fun () ->
        match Lazy.force tbl with None -> No_entry | Some t -> t.opened);
    tbl

  let memo cache f =
    let tbl = lazy_table cache in
    fun x ->
      record_lookup cache;
      match Lazy.force tbl with
      | None -> f x
      | Some tbl -> (
        try find tbl x
        with Not_found ->
          let res = f x in
          add tbl x res; res )

  (* A proof records the read whether [cond x] holds or not: with no table,
     [cond] is not evaluated. *)
  let memo_cond cache cond f =
    let tbl = lazy_table cache in
    fun x ->
      record_lookup cache;
      match Lazy.force tbl with
      | None -> f x
      | Some tbl ->
        if cond x then begin
          try find tbl x
          with Not_found ->
            let res = f x in
            add tbl x res; res
        end
        else f x
end

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
