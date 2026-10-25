(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* What a recorded read is worth now (BET-84, part P3). One evaluator per
   channel of the census. An evaluator answers [Unknown] rather than
   guessing: the proof then runs its tactics, as today. *)

open Names

let digest what v =
  match Proof_record.digest_value v with
  | d -> Proof_replay.Value (Some d)
  | exception Proof_record.Unhashable _ -> ignore what; Proof_replay.Unknown

let absent = Proof_replay.Value None

(* A kernel name the recorder printed, read back. [Nametab.global_of_path]
   finds what that absolute path names now; the printed name must come out
   the same, so a path that names something else is not taken for it. *)
let global_of_string s =
  match Nametab.global_of_path (Libnames.path_of_string s) with
  | g -> Some g
  | exception _ -> None

let constant_of_string s =
  match global_of_string s with
  | Some (GlobRef.ConstRef c) when String.equal (Constant.to_string c) s -> Some c
  | _ -> None

let mind_of_string s =
  match global_of_string s with
  | Some (GlobRef.IndRef (mind, _)) when String.equal (MutInd.to_string mind) s -> Some mind
  | Some (GlobRef.ConstructRef ((mind, _), _)) when String.equal (MutInd.to_string mind) s -> Some mind
  | _ -> None

let modpath_of_string s =
  match Nametab.locate_module (Libnames.qualid_of_string s) with
  | mp when String.equal (ModPath.to_string mp) s -> Some mp
  | _ -> None
  | exception _ -> None

(* Census row 1: the globals the proof looked up, each with the digest of
   what the lookup found. The digests are the ones [kernel/environ.ml]
   records. *)
let row1 () =
  let env () = Global.env () in
  Proof_replay.register_evaluator "constant" (fun key ->
      match constant_of_string key with
      | None -> Proof_replay.Unknown
      | Some c ->
        (match Environ.lookup_constant_opt c (env ()) with
         | None -> absent
         | Some cb -> digest "constant" cb));
  Proof_replay.register_evaluator "constant_exists" (fun key ->
      match constant_of_string key with
      | None -> Proof_replay.Unknown
      | Some c -> digest "constant_exists" (Environ.mem_constant c (env ())));
  Proof_replay.register_evaluator "rewrite_rules" (fun key ->
      match constant_of_string key with
      | None -> Proof_replay.Unknown
      | Some c ->
        (match Environ.lookup_rewrite_rules c (env ()) with
         | rs -> digest "rewrite_rules" rs
         | exception Not_found -> absent));
  Proof_replay.register_evaluator "inductive" (fun key ->
      match mind_of_string key with
      | None -> Proof_replay.Unknown
      | Some mind ->
        if not (Environ.mem_mind mind (env ())) then absent
        else digest "inductive" (Environ.lookup_mind mind (env ())));
  Proof_replay.register_evaluator "inductive_exists" (fun key ->
      match mind_of_string key with
      | None -> Proof_replay.Unknown
      | Some mind -> digest "inductive_exists" (Environ.mem_mind mind (env ())));
  Proof_replay.register_evaluator "module" (fun key ->
      match modpath_of_string key with
      | None -> Proof_replay.Unknown
      | Some mp ->
        (match Environ.lookup_module mp (env ()) with
         | m -> digest "module" m
         | exception Not_found -> absent));
  Proof_replay.register_evaluator "modtype" (fun key ->
      match modpath_of_string key with
      | None -> Proof_replay.Unknown
      | Some mp ->
        (match Environ.lookup_modtype mp (env ()) with
         | m -> digest "modtype" m
         | exception Not_found -> absent))

(* Row 5: how [simpl] unfolds a constant. Row 7: the hint database a
   search read. Row 15: the registered library references. *)
let tables () =
  Proof_replay.register_evaluator "reduction_behaviour" (fun key ->
      match constant_of_string key with
      | None -> Proof_replay.Unknown
      | Some c -> digest "reduction_behaviour" (Reductionops.ReductionBehaviour.get c));
  Proof_replay.register_evaluator "hint_db" (fun key ->
      match Hints.searchtable_map key with
      | db -> digest "hint_db" db
      | exception Not_found -> absent);
  Proof_replay.register_evaluator "lib_ref" (fun key ->
      match Rocqlib.lib_ref_opt key with
      | None -> absent
      | Some r -> digest "lib_ref" r)

(* The reads that have no single read point: the universe and quality
   graphs, the named context, the typing flags, the options, and, with
   -proof-record-tables, every hint database and typeclass table at the
   proof's start. Both sides take them from the same function, so they
   cannot drift apart. *)
let providers () =
  Proof_replay.register_provider Proof_record_env.start_reads;
  Proof_replay.register_provider Proof_recorder.table_reads

let init () =
  row1 ();
  tables ();
  providers ()
