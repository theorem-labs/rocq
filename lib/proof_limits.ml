(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let unknown = "unknown"

(* Reads a whole small file. [None] when it cannot be read. The files under
   /proc and /sys report a length of zero, so the bytes are read in a loop
   and not with [in_channel_length]. *)
let read_file path =
  match open_in_bin path with
  | exception Sys_error _ -> None
  | ic ->
    let buf = Buffer.create 4096 in
    let chunk = Bytes.create 4096 in
    let rec loop () =
      let n = input ic chunk 0 (Bytes.length chunk) in
      if n > 0 then (Buffer.add_subbytes buf chunk 0 n; loop ())
    in
    let res = match loop () with
      | () -> Some (Buffer.contents buf)
      | exception (End_of_file | Sys_error _) -> Some (Buffer.contents buf)
    in
    close_in_noerr ic;
    (match res with Some "" -> None | r -> r)

let trim_opt = function None -> None | Some s -> Some (String.trim s)

let is_blank = function ' ' | '\t' -> true | _ -> false

let words s = List.filter (fun w -> w <> "") (String.split_on_char ' ' (String.map (fun c -> if is_blank c then ' ' else c) s))

(* Peak resident set, in kB, from /proc/self/status. 0 when it is absent. *)
let peak_rss_kb () =
  match read_file "/proc/self/status" with
  | None -> 0
  | Some text ->
    let rec look = function
      | [] -> 0
      | line :: rest ->
        (match String.index_opt line ':' with
         | Some i when String.sub line 0 i = "VmHWM" ->
           (match words (String.sub line (i + 1) (String.length line - i - 1)) with
            | n :: _ -> (match int_of_string_opt n with Some v -> v | None -> 0)
            | [] -> 0)
         | Some _ | None -> look rest)
    in
    look (String.split_on_char '\n' text)

(* /proc/self/limits is a fixed-column table:
     Limit                     Soft Limit  Hard Limit  Units
     Max stack size            8388608     unlimited   bytes
   The soft limit starts at the "Soft Limit" column. A name can hold
   spaces, so the value is read from that column, not by splitting. *)
let rlimit name =
  match read_file "/proc/self/limits" with
  | None -> unknown
  | Some text ->
    let lines = String.split_on_char '\n' text in
    match lines with
    | [] -> unknown
    | head :: rows ->
      let soft_col =
        let rec find i =
          if i + 10 > String.length head then None
          else if String.sub head i 10 = "Soft Limit" then Some i
          else find (i + 1)
        in
        find 0
      in
      match soft_col with
      | None -> unknown
      | Some col ->
        let value row =
          if String.length row <= col then unknown
          else
            match words (String.sub row col (String.length row - col)) with
            | w :: _ -> w
            | [] -> unknown
        in
        let rec look = function
          | [] -> unknown
          | row :: rest ->
            if String.length row >= String.length name && String.sub row 0 (String.length name) = name
            then value row
            else look rest
        in
        look rows

(* cgroup v2: /proc/self/cgroup holds one line "0::<path>", and the cap is
   <mount>/<path>/memory.max. The usual mount is /sys/fs/cgroup. The
   process's own cgroup directory is tried first, because a container sees
   its cgroup as the root. *)
let memory_cap () =
  let direct = trim_opt (read_file "/sys/fs/cgroup/memory.max") in
  let from_path () =
    match trim_opt (read_file "/proc/self/cgroup") with
    | None -> None
    | Some text ->
      let line = match String.split_on_char '\n' text with l :: _ -> l | [] -> "" in
      match String.rindex_opt line ':' with
      | None -> None
      | Some i ->
        let path = String.sub line (i + 1) (String.length line - i - 1) in
        trim_opt (read_file (Filename.concat "/sys/fs/cgroup" (Filename.concat path "memory.max")))
  in
  match direct with
  | Some v when v <> "" -> v
  | Some _ | None -> (match from_path () with Some v when v <> "" -> v | Some _ | None -> unknown)

let overcommit_memory () =
  match trim_opt (read_file "/proc/sys/vm/overcommit_memory") with
  | Some v when v <> "" -> v
  | Some _ | None -> unknown
