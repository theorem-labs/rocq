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

let scheme_map = Summary.ref Indmap_env.empty ~name:"Schemes"

let cache_one_scheme kind (ind,const) =
  scheme_map := Indmap_env.update ind (function
      | None -> Some (CString.Map.singleton kind const)
      | Some map -> Some (CString.Map.add kind const map))
      !scheme_map

let cache_scheme (kind,l) =
  cache_one_scheme kind l

let subst_one_scheme subst (ind,const) =
  (* Remark: const is a def: the result of substitution is a constant *)
  (Mod_subst.subst_ind subst ind, Globnames.subst_global_reference subst const)

let subst_scheme (subst,(kind,l)) =
  (kind, subst_one_scheme subst l)

let inScheme : Libobject.locality * (string * (inductive * GlobRef.t)) -> Libobject.obj =
  let open Libobject in
  declare_object @@ object_with_locality "SCHEME"
    ~cache:cache_scheme
    ~subst:(Some subst_scheme)
    ~discharge:(fun x -> x)

let declare_scheme local kind indcl =
  Lib.add_leaf (inScheme (local,(kind,indcl)))

(* BET-84 census row 15: each scheme the proof looks up, by kind and
   inductive, absent when it is not yet declared. ONE value function,
   called by the record site here and by the replay evaluator
   (dev/tools/census/replay_channels.py). *)
let recorded_scheme kind ind =
  match Indmap_env.find_opt ind !scheme_map with
  | None -> None
  | Some m ->
    (match CString.Map.find_opt kind m with
     | None -> None
     | Some c -> Some (Pp.string_of_ppcmds (GlobRef.print c)))

(* The key is ["<kind>:<inductive path>,<index>"]. A key that does not read
   back to the same inductive is not taken for another: the proof misses. *)
let key_of_string key =
  match String.index_opt key ':', String.rindex_opt key ',' with
  | Some i, Some j when j > i ->
    let kind = String.sub key 0 i in
    let path = String.sub key (i + 1) (j - i - 1) in
    let index = String.sub key (j + 1) (String.length key - j - 1) in
    (match Nametab.global_of_path (Libnames.path_of_string path), int_of_string_opt index with
     | (GlobRef.IndRef (m, _) | GlobRef.ConstructRef ((m, _), _)), Some n
       when String.equal (MutInd.to_string m) path -> Some (kind, (m, n))
     | _ -> None
     | exception _ -> None)
  | _ -> None

let () =
  Proof_replay.register_evaluator "scheme" (fun key ->
      match key_of_string key with
      | None -> Proof_replay.Unknown
      | Some (kind, ind) ->
        (match recorded_scheme kind ind with
         | v -> Proof_replay.Value v
         | exception _ -> Proof_replay.Unknown))

let lookup_scheme kind ind =
  if Proof_recorder.active () then begin
    let res =
      match Indmap_env.find_opt ind !scheme_map with
      | None -> None
      | Some m -> CString.Map.find_opt kind m
    in
    Proof_recorder.read ~row:"15" ~channel:"scheme"
      ~key:(fun () -> kind ^ ":" ^ MutInd.to_string (fst ind) ^ "," ^ string_of_int (snd ind))
      ~value:(fun () -> recorded_scheme kind ind);
    (match res with Some c -> c | None -> raise Not_found)
  end else
    CString.Map.find kind (Indmap_env.find ind !scheme_map)

let lookup_scheme_opt kind ind =
  try Some (lookup_scheme kind ind) with Not_found -> None

let all_schemes () = !scheme_map
