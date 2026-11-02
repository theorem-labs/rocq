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

(* BET-84 census row 23. A lookup gives what the prover computes, or an
   entry of the cache file. [open_in] loads only each entry's hash and
   position, and [find] reads the entry from the file at the first lookup
   that needs it. That read can come long after the table opened, and the
   file can change between the two (a command that writes a file truncates
   it), so nothing that the opening saw fixes what a later lookup gets. An
   entry that this process adds is kept in memory and is never read back.

   So a table that opened with no entry gives only what this process's
   prover computed, and a table that never opens reads no file. Replay can
   rely on a table only in these cases. The fence check below trips the
   process-wide fence (reason [micromega_cache], detail the file) in the
   two other cases:
   - a table loaded entries from its file when it opened;
   - no table has opened a cache path, and that path holds a file (not a
     directory). A replayed proof does not open the table where stock
     opens it, so a file there could give stock an entry that the
     registration never read.
   The check runs at each recorded proof's start and end and at each
   replay decision (Proof_recorder.register_fence_check). The grading
   engine makes each cache path a directory, so the table cannot open, the
   check finds no file, and no proof loses its replay. *)
type table =
  | Unopened
  | Fresh (* opened with no entry, or its file could not be opened *)
  | Loaded (* opened with entries of its file *)

(* Each memo function's file and the state of its table. *)
let caches : (string * (unit -> table)) list ref = ref []

let register_cache file table = caches := (file, table) :: !caches

(* Whether [path] holds something other than a directory. A stat that fails
   for another reason than an absent path counts as a file. *)
let holds_file path =
  match Unix.stat path with
  | { Unix.st_kind = Unix.S_DIR; _ } -> false
  | _ -> true
  | exception Unix.Unix_error (Unix.ENOENT, _, _) -> false
  | exception Unix.Unix_error _ -> true

let () =
  Proof_recorder.register_fence_check (fun () ->
      List.iter (fun (file, table) ->
          let trip = match table () with
            | Loaded -> true
            | Fresh -> false
            | Unopened -> holds_file file
          in
          if trip then Proof_recorder.trip_fence ~reason:"micromega_cache" ~detail:file)
        !caches)

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
               loaded : bool (* BET-84: the table loaded entries of [file] *) }

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
      let htbl = do_under_lock Read finch (fun () ->
          let table = Table.empty in
          if check_magic_number_and_version inch
          then xload table
          else raise InvalidTableFormat
        ) in
      let () = close_in_noerr inch in
      let outch = out_channel_of_descr (openfile f [O_WRONLY; O_APPEND; O_CREAT] 0o666) in
      let htbl = Option.default Table.empty htbl in
      { outch ; file = f; htbl; loaded = not (Table.is_empty htbl) }
    with InvalidTableFormat ->
      let () = close_in_noerr inch in
      let flags = [O_WRONLY; O_TRUNC; O_APPEND; O_CREAT] in
      let out = openfile f flags 0o666 in
      let outch = out_channel_of_descr out in
      output_int32 outch ObjFile.magic_number;
      output_int32 outch pcache_version;
      {outch; htbl=Table.empty; file = f; loaded = false}

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

  (* The table [cache] names, opened at the first lookup. The fence check
     reads its state (BET-84 census row 23). *)
  let lazy_table cache =
    let tbl = lazy (try Some (open_in cache) with e when CErrors.noncritical e -> None) in
    register_cache cache (fun () ->
        if not (Lazy.is_val tbl) then Unopened
        else match Lazy.force tbl with
          | Some { loaded = true; _ } -> Loaded
          | Some { loaded = false; _ } | None -> Fresh);
    tbl

  let memo cache f =
    let tbl = lazy_table cache in
    fun x ->
      match Lazy.force tbl with
      | None -> f x
      | Some tbl -> (
        try find tbl x
        with Not_found ->
          let res = f x in
          add tbl x res; res )

  let memo_cond cache cond f =
    let tbl = lazy_table cache in
    fun x ->
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
