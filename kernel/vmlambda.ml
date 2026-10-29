open Util
open Declarations
open Genlambda
open Vmvalues

type lval = int * structured_values (* keep the hash *)
type lambda = lval Genlambda.lambda

let get_lval (_, v) = v

(** Simplification of lambda expression *)

(*s Translation from [constr] to [lambda] *)

(* Translation of constructor *)

let is_value lc =
  match node lc with
  | Lval _ | Lint _ | Luint _ | Lfloat _ | Lstring _ -> true
  | _ -> false

let get_value lc =
  match node lc with
  | Luint i -> val_of_uint i
  | Lval (_, v) -> v
  | Lint i -> val_of_int i
  | Lfloat f -> val_of_float f
  | Lstring s -> val_of_string s
  | _ -> assert false

let hash_block tag args =
  let open Hashset.Combine in
  let fold accu v =
    let h = match node v with
    | Luint i -> Uint63.hash i
    | Lint i -> Hashtbl.hash (i : int)
    | Lfloat f -> Float64.hash f
    | Lstring s -> Pstring.hash s
    | Lval (h, _) -> h
    | _ -> assert false
    in
    combine accu h
  in
  (* [combine] is linear, so the hash is mixed at every level: an [Lval]
     carries the hash of its block. Unmixed, a block of tag 0 with one field
     had the hash of that field (S n that of n, xI p that of p), and xO p that
     of p plus a constant, so every positive with as many xO had one hash. *)
  Hashtbl.hash (combine tag (Array.fold_left fold 0 args))

(* Structured constants of the same tag whose arguments are physically
   equal are shared, within one compilation: the table is strong and
   [lambda_of_constr] empties it when it starts. It cannot empty it when it
   ends: [Vmbytegen] calls [as_value] for an [Lparray] after the lambda,
   in the same compilation.

   It was a weak set kept for the life of the process, whose elements were
   the triples [(tag, args, block)] built here. Nothing else refers to a
   triple, so an entry died at the next minor collection unless one ran
   during a lookup and promoted it; a promoted entry then lived as long as
   lookups of its hash read it while the major GC was marking, since a weak
   get darkens what it returns. With the unmixed hash, hundreds of distinct
   constants stayed alive under one hash, and every lookup of that hash
   read them all: 30 to 45 weak gets per lookup, and 195 to 275 s of the
   workers' time in a coqchk -j 16 of a large development, varying from run
   to run with what the main process held when it forked. *)
module HashBlock =
struct
  type t = int * int * structured_values array (* hash, tag, arguments *)
  let equal (h1, tag1, args1) (h2, tag2, args2) =
    Int.equal h1 h2 && Int.equal tag1 tag2 && CArray.equal (==) args1 args2
  let hash (h, _, _) = h
end

module BlockTable = Hashtbl.Make(HashBlock)

let block_table : structured_values BlockTable.t = BlockTable.create 97

let as_value tag args =
  if Array.for_all is_value args then
    let h = hash_block tag args in
    (* Don't simplify this to Array.map because of flat float arrays *)
    let args =
      let dummy_val = Obj.magic 0 in
      let ans = Array.make (Array.length args) dummy_val in
      let () = Array.iteri (fun i v -> ans.(i) <- get_value v) args in
      ans
    in
    let block_tag, args =
      if tag < Obj.last_non_constant_constructor_tag then tag, args
      else
        Obj.last_non_constant_constructor_tag,
        Array.append [| val_of_int (tag - Obj.last_non_constant_constructor_tag) |] args
    in
    let key = (h, tag, args) in
    match BlockTable.find_opt block_table key with
    | Some block -> Some (h, block)
    | None ->
      let block = val_of_block block_tag args in
      let () = BlockTable.add block_table key block in
      Some (h, block)
  else None

module Val =
struct
  type value = int * structured_values
  let as_value = as_value
  let check_inductive (_, i) mb =
    let { mind_typename=name; mind_nb_args; mind_nb_constant; _ } = mb.mind_packets.(i) in
    Vmerrors.check_compilable_ind ~name ~mind_nb_args ~mind_nb_constant
end

module Lambda = Genlambda.Make(Val)

(*********************************)
let dump_lambda_flag, dump_lambda = CDebug.create_full ~name:"vmlambda" ()

let lambda_of_constr ~inline_limit env sigma c =
  let () = BlockTable.reset block_table in
  let lam = Lambda.lambda_of_constr ~inline_limit env sigma c in
  let lam = optimize lam in
  dump_lambda (fun () -> pp_lam lam);
  lam
