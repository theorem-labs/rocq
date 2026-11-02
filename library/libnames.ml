(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

(**********************************************)

(*s Operations on dirpaths *)

let split_dirpath d = match DirPath.repr d with
  | id :: l -> DirPath.make l, id
  | _ -> failwith "split_dirpath"

let pop_dirpath p = match DirPath.repr p with
  | _::l -> DirPath.make l
  | [] -> failwith "pop_dirpath"

(* Pop the last n module idents *)
let pop_dirpath_n n dir = DirPath.make (List.skipn n (DirPath.repr dir))

let is_dirpath_prefix_of d1 d2 =
  List.prefix_of Id.equal
    (List.rev (DirPath.repr d1)) (List.rev (DirPath.repr d2))

let is_dirpath_suffix_of dir1 dir2 =
  let dir1 = DirPath.repr dir1 in
  let dir2 = DirPath.repr dir2 in
  List.prefix_of Id.equal dir1 dir2

let drop_dirpath_prefix d1 d2 =
  let d =
    List.drop_prefix Id.equal
      (List.rev (DirPath.repr d1)) (List.rev (DirPath.repr d2))
  in
  DirPath.make (List.rev d)

let append_dirpath d1 d2 = DirPath.make (DirPath.repr d2 @ DirPath.repr d1)

let add_dirpath_suffix p id = DirPath.make (id :: DirPath.repr p)

(* parsing *)
let parse_dir s =
  let len = String.length s in
  let rec decoupe_dirs dirs n =
    if Int.equal n len && n > 0 then
      CErrors.user_err Pp.(str @@ s ^ " is an invalid path.");
    if n >= len then dirs else
    let pos =
      try
        String.index_from s n '.'
      with Not_found -> len
    in
    if Int.equal pos n then
      CErrors.user_err Pp.(str @@ s ^ " is an invalid path.");
    let dir = String.sub s n (pos-n) in
    decoupe_dirs ((Id.of_string dir)::dirs) (pos+1)
  in
    decoupe_dirs [] 0

let dirpath_of_string s =
  let path = match s with
  | "" -> []
  | _ -> parse_dir s
  in
  DirPath.make path

(** Absolute paths *)

type full_path = {
  dirpath : DirPath.t;
  basename : Id.t;
}

let dirpath sp = sp.dirpath
let basename sp = sp.basename

let dirpath_of_path { dirpath; basename } =
  add_dirpath_suffix dirpath basename

let is_path_prefix_of p dp = is_dirpath_prefix_of (dirpath_of_path p) dp

let make_path pa id = { dirpath = pa; basename = id }

let make_path0 dp =
  let dp, id = split_dirpath dp in
  make_path dp id

let dummy_full_path = make_path0 DirPath.dummy

let add_path_suffix { dirpath = pa0; basename = id0 } id =
  { dirpath = add_dirpath_suffix pa0 id0; basename = id }

let append_path ({ dirpath = dp; basename = id0 } as p) dp' =
  if DirPath.is_empty dp' then p
  else
    let dp', id = split_dirpath dp' in
    { dirpath = append_dirpath (add_dirpath_suffix dp id0) dp'; basename = id }

let path_pop_n_suffixes n ({ dirpath = dp; } as path) =
  if n = 0 then path
  else
    let dp = pop_dirpath_n (n-1) dp in
    make_path0 dp

let path_pop_suffix p = path_pop_n_suffixes 1 p

let repr_path { dirpath = pa; basename = id } = (pa,id)

let eq_full_path p1 p2 =
  Id.equal p1.basename p2.basename &&
  DirPath.equal p1.dirpath p2.dirpath

(* parsing and printing of section paths *)
let string_of_path sp =
  let (sl,id) = repr_path sp in
  match DirPath.repr sl with
  | [] -> Id.to_string id
  | _ -> (DirPath.to_string sl) ^ "." ^ (Id.to_string id)

let compare_full_path sp1 sp2 =
  let (p1,id1) = repr_path sp1
  and (p2,id2) = repr_path sp2 in
  let p_bit = DirPath.compare p1 p2 in
  if Int.equal p_bit 0 then Id.compare id1 id2 else p_bit

module SpOrdered =
  struct
    type t = full_path
    let compare = compare_full_path
  end

module Spmap = Map.Make(SpOrdered)

let path_of_string s =
  try
    let dir, id = split_dirpath (dirpath_of_string s) in
    make_path dir id
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let pr_path sp = Pp.str (string_of_path sp)

(*s qualified names *)
type qualid_r = full_path
type qualid = qualid_r CAst.t

let make_qualid ?loc pa id = CAst.make ?loc (make_path pa id)
let repr_qualid {CAst.v=qid} = repr_path qid

let qualid_eq qid1 qid2 = eq_full_path qid1.CAst.v qid2.CAst.v

let is_qualid_suffix_of_full_path
    CAst.{v={dirpath=dirpath1;basename=basename1}} {dirpath=dirpath2;basename=basename2} =
  let dir1 = DirPath.repr dirpath1 in
  let dir2 = DirPath.repr dirpath2 in
  Id.equal basename1 basename2 && List.prefix_of Id.equal dir1 dir2

let string_of_qualid qid = string_of_path qid.CAst.v
let pr_qualid qid = pr_path qid.CAst.v

let qualid_of_string ?loc s = CAst.make ?loc @@ path_of_string s

let qualid_of_path ?loc sp = CAst.make ?loc sp
let qualid_of_ident ?loc id = make_qualid ?loc DirPath.empty id
let qualid_of_dirpath ?loc dir =
  let (l,a) = split_dirpath dir in
  make_qualid ?loc l a

let qualid_of_lident lid = qualid_of_ident ?loc:lid.CAst.loc lid.CAst.v

let qualid_is_ident qid = DirPath.is_empty (dirpath qid.CAst.v)

let qualid_basename qid =
  qid.CAst.v.basename

let qualid_path qid =
  qid.CAst.v.dirpath

let idset_mem_qualid qid s =
  qualid_is_ident qid && Id.Set.mem (qualid_basename qid) s

(* Default paths *)

(*s Roots of the space of absolute names *)
let rocq_init_string = "Corelib"
let rocq_init_root = Id.of_string rocq_init_string
let default_root_prefix = DirPath.empty

(* BET-84 P3: a kernel name as a recorded key, and back.
   [KerName.to_string] is not a key: it drops a bound module's number, and
   ["A.B.c"] is both the label [c] of the file [A.B] and the label [c] of the
   module [B] of the file [A]. So each part is written with its length
   ([<length>:<bytes>]): the label, then the module path, which is
   [F<n>:] and the [n] parts of a file's directory path, outermost first;
   [D<label>] and the path of the module it is in; or [B] and a bound
   module's number, name and file. No key is a prefix of another, so a key
   names one kernel name. *)
let key_part s = string_of_int (String.length s) ^ ":" ^ s

let rec modpath_key = function
  | ModPath.MPfile dp ->
    let ids = List.rev (DirPath.repr dp) in
    "F" ^ string_of_int (List.length ids) ^ ":"
    ^ String.concat "" (List.map (fun id -> key_part (Id.to_string id)) ids)
  | ModPath.MPbound mbid ->
    let (n, id, dp) = MBId.repr mbid in
    "B" ^ key_part (string_of_int n) ^ key_part (Id.to_string id) ^ modpath_key (ModPath.MPfile dp)
  | ModPath.MPdot (mp, l) -> "D" ^ key_part (Id.to_string l) ^ modpath_key mp

let kername_key kn = key_part (Id.to_string (KerName.label kn)) ^ modpath_key (KerName.modpath kn)

(* The reader of [kername_key], from byte [start] of [key]: the kernel name
   and the position after it. A bound module cannot be rebuilt from its
   number, so its key reads back to nothing; so does a part that is not an
   identifier [Id.of_string_soft] accepts. *)
let kername_parse key start =
  let n = String.length key in
  let pos = ref start in
  let number () =
    match String.index_from_opt key !pos ':' with
    | None -> None
    | Some j ->
      let v = int_of_string_opt (String.sub key !pos (j - !pos)) in
      pos := j + 1;
      (match v with Some v when v >= 0 -> Some v | Some _ | None -> None)
  in
  let part () =
    match number () with
    | Some len when !pos + len <= n ->
      let s = String.sub key !pos len in
      pos := !pos + len;
      (match Id.of_string_soft s with
       | id -> Some id
       | exception CErrors.UserError _ -> None)
    | Some _ | None -> None
  in
  let rec parts k acc =
    if k = 0 then Some acc
    else match part () with None -> None | Some id -> parts (k - 1) (id :: acc)
  in
  let rec modpath () =
    if !pos >= n then None
    else begin
      let tag = key.[!pos] in
      incr pos;
      match tag with
      | 'F' ->
        (match number () with
         | None -> None
         | Some k -> Option.map (fun ids -> ModPath.MPfile (DirPath.make ids)) (parts k []))
      | 'D' ->
        (match part () with
         | None -> None
         | Some l -> Option.map (fun mp -> ModPath.MPdot (mp, l)) (modpath ()))
      | _ -> None
    end
  in
  match part () with
  | None -> None
  | Some l -> Option.map (fun mp -> (KerName.make mp l, !pos)) (modpath ())

let kername_of_key key =
  match kername_parse key 0 with
  | Some (kn, e) when e = String.length key && String.equal (kername_key kn) key -> Some kn
  | Some _ | None -> None

(* BET-84: a constant as a recorded key: its user and canonical kernel
   names, each as [kername_key] writes it. Two constants with the same user
   name and different canonical names (an alias of a module) get different
   keys. *)
let constant_key c =
  kername_key (Constant.user c) ^ kername_key (Constant.canonical c)

(* A constant or a mutual inductive (a kernel pair) from byte [start] of
   [key]: its user kernel name, then its canonical one, and the position
   after them. *)
let kerpair_parse make key start =
  match kername_parse key start with
  | None -> None
  | Some (user, e) ->
    Option.map (fun (canonical, e') -> (make user canonical, e')) (kername_parse key e)

let constant_of_key key =
  match kerpair_parse Constant.make key 0 with
  | Some (c, e) when e = String.length key && String.equal (constant_key c) key -> Some c
  | Some _ | None -> None

(* BET-84: a global reference as a recorded key, read back without the
   nametab: [V] and a variable's name; [C] and the constant's key; [I], the
   user and canonical kernel names of the mutual inductive, and the index of
   the inductive; [K], the same, and the index of the constructor. Every
   part is written with its length, so a key names one reference. *)
let mutind_key m = kername_key (MutInd.user m) ^ kername_key (MutInd.canonical m)

let globref_key = function
  | GlobRef.VarRef id -> "V" ^ key_part (Id.to_string id)
  | GlobRef.ConstRef c -> "C" ^ constant_key c
  | GlobRef.IndRef (m, i) -> "I" ^ mutind_key m ^ key_part (string_of_int i)
  | GlobRef.ConstructRef ((m, i), j) ->
    "K" ^ mutind_key m ^ key_part (string_of_int i) ^ key_part (string_of_int j)

(* One [<length>:<bytes>] part from byte [start] of [key]: its bytes and the
   position after it. *)
let part_parse key start =
  let n = String.length key in
  if start >= n then None
  else match String.index_from_opt key start ':' with
    | None -> None
    | Some j ->
      match int_of_string_opt (String.sub key start (j - start)) with
      | Some len when len >= 0 && j + 1 + len <= n -> Some (String.sub key (j + 1) len, j + 1 + len)
      | Some _ | None -> None

let index_parse key start =
  Option.bind (part_parse key start) (fun (s, e) ->
      Option.map (fun i -> (i, e)) (int_of_string_opt s))

(* The whole key must be read, and the reference read back must give the
   key again. *)
let globref_of_key key =
  let n = String.length key in
  let whole = function Some (r, e) when e = n -> Some r | Some _ | None -> None in
  let parsed =
    if n = 0 then None
    else match key.[0] with
      | 'V' ->
        whole (Option.bind (part_parse key 1) (fun (s, e) ->
            match Id.of_string_soft s with
            | id -> Some (GlobRef.VarRef id, e)
            | exception CErrors.UserError _ -> None))
      | 'C' ->
        whole (Option.map (fun (c, e) -> (GlobRef.ConstRef c, e)) (kerpair_parse Constant.make key 1))
      | 'I' ->
        whole (Option.bind (kerpair_parse MutInd.make key 1) (fun (m, e) ->
            Option.map (fun (i, e) -> (GlobRef.IndRef (m, i), e)) (index_parse key e)))
      | 'K' ->
        whole (Option.bind (kerpair_parse MutInd.make key 1) (fun (m, e) ->
            Option.bind (index_parse key e) (fun (i, e) ->
                Option.map (fun (j, e) -> (GlobRef.ConstructRef ((m, i), j), e)) (index_parse key e))))
      | _ -> None
  in
  match parsed with
  | Some r when String.equal (globref_key r) key -> Some r
  | Some _ | None -> None
