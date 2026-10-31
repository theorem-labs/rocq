(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Reserved names *)

open CErrors
open Util
open Pp
open Names
open Nameops
open Notation_term
open Notation_ops

type key =
  | RefKey of GlobRef.t
  | Oth

(** TODO: share code from Notation *)

let canonize_key env k = match k with
| Oth -> Oth
| RefKey gr ->
  let gr' = Environ.QGlobRef.canonize env gr in
  if gr' == gr then k else RefKey gr'

let mkRefKey env gr =
  RefKey (Environ.QGlobRef.canonize env gr)

let key_compare k1 k2 = match k1, k2 with
| RefKey gr1, RefKey gr2 -> GlobRef.UserOrd.compare gr1 gr2
| RefKey _, Oth -> -1
| Oth, RefKey _ -> 1
| Oth, Oth -> 0

module KeyOrd = struct type t = key let compare = key_compare end
module KeyMap = Map.Make(KeyOrd)

module ReservedSet :
sig
  type t
  val empty : t
  val add : (Id.t * notation_constr) -> t -> t
  val find : (Id.t -> notation_constr -> bool) -> t -> Id.t * notation_constr
end =
struct
  type t = (Id.t * notation_constr) list

  let empty = []

  let rec mem id c = function
  | [] -> false
  | (id', c') :: l ->
    if c == c' && Id.equal id id' then true else mem id c l

  let add p l =
    let (id, c) = p in
    if mem id c l then l else p :: l

  let rec find f = function
  | [] -> raise Not_found
  | (id, c) as p :: l -> if f id c then p else find f l
end


let keymap_add env key data map =
  let key = canonize_key env key in
  let old = try KeyMap.find key map with Not_found -> ReservedSet.empty in
  KeyMap.add key (ReservedSet.add data old) map

let reserve_table = Summary.ref Id.Map.empty ~name:"reserved-type"
let reserve_revtable = Summary.ref KeyMap.empty ~name:"reserved-type-rev"

let notation_constr_key env = function (* Rem: NApp(NRef ref,[]) stands for @ref *)
  | NApp (NRef (ref,_),args) -> mkRefKey env ref, Some (List.length args)
  | NList (_,_,NApp (NRef (ref,_),args),_,_)
  | NBinderList (_,_,NApp (NRef (ref,_),args),_,_) -> mkRefKey env ref, Some (List.length args)
  | NRef (ref,_) -> mkRefKey env ref, None
  | _ -> Oth, None

let add_reserved_type env (id,t) =
  let key = fst (notation_constr_key env t) in
  reserve_table := Id.Map.add id t !reserve_table;
  reserve_revtable := keymap_add env key (id, t) !reserve_revtable

let declare_reserved_type_binding env {CAst.loc;v=id} t =
  if not (Id.equal id (root_of_id id)) then
    user_err ?loc
      ((Id.print id ++ str
      " is not reservable: it must have no trailing digits, quote, or _."));
  begin try
    let _ = Id.Map.find id !reserve_table in
    user_err ?loc
    ((Id.print id ++ str " is already bound to a type."))
  with Not_found -> () end;
  add_reserved_type env (id,t)

let declare_reserved_type idl t =
  let env = Global.env () in
  List.iter (fun id -> declare_reserved_type_binding env id t) (List.rev idl)

(* BET-84 row M2: each reserved type ([Implicit Types]) the proof reads,
   keyed by the root of the identifier, which is the table's own key. ONE
   value function, called by the record site and by the replay evaluator
   (dev/tools/census/replay_channels.py). *)
let recorded_reserved_type root =
  Option.map (fun t -> Proof_recorder.digest ~what:"reserved_type" t)
    (Id.Map.find_opt root !reserve_table)

(* The key is the root as a string; the table is keyed by [Id.t], which is a
   string, so the key reads back exactly. A string no identifier can be is
   a miss. *)
let () =
  Proof_replay.register_evaluator "reserved_type" (fun key ->
      match Id.of_string_soft key with
      | root -> Proof_replay.Value (recorded_reserved_type root)
      | exception CErrors.UserError _ -> Proof_replay.Unknown)

let find_reserved_type id =
  let root = root_of_id id in
  if Proof_recorder.active () then
    Proof_recorder.read ~row:"M2" ~channel:"reserved_type"
      ~key:(fun () -> Id.to_string root)
      ~value:(fun () -> recorded_reserved_type root);
  Id.Map.find root !reserve_table

let constr_key env evd c =
  try mkRefKey env (fst @@ EConstr.destRef evd (fst (EConstr.decompose_app evd c)))
  with Constr.DestKO -> Oth

(* BET-84 row M2: the reverse table, read when a binder with no name gets
   the name reserved for its type ([Namegen.next_name_away_with_default_using_types]:
   the lambda that refines a function evar, and the index that an [in]
   clause matches against a pattern). The name reaches the proof term, so
   the stock term differs when the reservation changes (gate review, breadth
   audit gap CF6; fixtures verdict_reserved_type_rev,
   verdict_reserved_type_rev_in). The key is the head the table is keyed by:
   [O] for a head that is not a reference, else the reference's kind and
   user names (the map compares references by their user names), each part
   with its length, as [Libnames.kername_key] writes a kernel name;
   [rev_key_of_string] reads it back. The value is the table's entry for
   that head: every reserved name with its type, in order, absent included.
   ONE value function, called by the record site and by the replay evaluator
   (dev/tools/census/replay_channels.py). *)
let rev_key_string k =
  let part s = string_of_int (String.length s) ^ ":" ^ s in
  let int i = part (string_of_int i) in
  match k with
  | Oth -> "O"
  | RefKey (GlobRef.VarRef id) -> "V" ^ part (Id.to_string id)
  | RefKey (GlobRef.ConstRef c) -> "C" ^ part (Libnames.kername_key (Constant.user c))
  | RefKey (GlobRef.IndRef (m, i)) -> "I" ^ part (Libnames.kername_key (MutInd.user m)) ^ int i
  | RefKey (GlobRef.ConstructRef ((m, i), j)) ->
    "K" ^ part (Libnames.kername_key (MutInd.user m)) ^ int i ^ int j

let rev_key_of_string s =
  let n = String.length s in
  let pos = ref 1 in
  let part () =
    match String.index_from_opt s !pos ':' with
    | None -> None
    | Some j ->
      match int_of_string_opt (String.sub s !pos (j - !pos)) with
      | Some len when len >= 0 && j + 1 + len <= n ->
        pos := j + 1 + len;
        Some (String.sub s (j + 1) len)
      | Some _ | None -> None
  in
  let int () = Option.bind (part ()) int_of_string_opt in
  let kn () = Option.bind (part ()) Libnames.kername_of_key in
  let k =
    if Int.equal n 0 then None
    else match s.[0] with
      | 'O' -> Some Oth
      | 'V' ->
        Option.bind (part ()) (fun p ->
            match Id.of_string_soft p with
            | id -> Some (RefKey (GlobRef.VarRef id))
            | exception CErrors.UserError _ -> None)
      | 'C' -> Option.map (fun kn -> RefKey (GlobRef.ConstRef (Constant.make1 kn))) (kn ())
      | 'I' ->
        (match kn () with
         | None -> None
         | Some kn -> Option.map (fun i -> RefKey (GlobRef.IndRef (MutInd.make1 kn, i))) (int ()))
      | 'K' ->
        (match kn () with
         | None -> None
         | Some kn ->
           match int () with
           | None -> None
           | Some i ->
             Option.map (fun j -> RefKey (GlobRef.ConstructRef ((MutInd.make1 kn, i), j))) (int ()))
      | _ -> None
  in
  match k with
  | Some k when Int.equal !pos n && String.equal (rev_key_string k) s -> Some k
  | Some _ | None -> None

let recorded_reserved_type_rev k =
  Option.map (fun set -> Proof_recorder.digest ~what:"reserved_type_rev" set)
    (KeyMap.find_opt k !reserve_revtable)

let () =
  Proof_replay.register_evaluator "reserved_type_rev" (fun key ->
      match rev_key_of_string key with
      | None -> Proof_replay.Unknown
      | Some k -> Proof_replay.Value (recorded_reserved_type_rev k))

let revert_reserved_type env evd t =
  let key = constr_key env evd t in
  if Proof_recorder.active () then
    Proof_recorder.read ~row:"M2" ~channel:"reserved_type_rev"
      ~key:(fun () -> rev_key_string key)
      ~value:(fun () -> recorded_reserved_type_rev key);
  try
    let reserved = KeyMap.find key !reserve_revtable in
    let t = Detyping.detype Detyping.Now ~flags:(PrintingFlags.Detype.current()) env evd t in
    let factorize_eqns = PrintingFlags.Extern.FactorizeEqns.current() in
    (* pedrot: if [Notation_ops.match_notation_constr] may raise [Failure _]
        then I've introduced a bug... *)
    let filter _ pat =
      try
        let _ : _ * _ * _ * _ =
          match_notation_constr ~print_parentheses:true ~factorize_eqns t ~vars:Id.Set.empty ([], pat)
        in
        true
      with No_match -> false
    in
    let (id, _) = ReservedSet.find filter reserved in
    Name id
  with Not_found | Failure _ -> Anonymous

let () = Namegen.set_reserved_typed_name revert_reserved_type
