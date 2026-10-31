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
open Pp
open CErrors
open Names
open Proofview.Notations
open Tac2expr
open Tac2val
open Tac2bt

exception LtacError = Tac2ffi.LtacError

module IdMap = Tac2env.IdMap

type environment = Tac2env.environment = {
  env_ist : valexpr IdMap.t;
}

let empty_environment = {
  env_ist = IdMap.empty;
}

type closure = {
  mutable clos_env : valexpr IdMap.t;
  (** Mutable so that we can implement recursive functions imperatively *)
  clos_var : Name.t list;
  (** Bound variables *)
  clos_exp : glb_tacexpr;
  (** Body *)
  clos_ref : ltac_constant option;
  (** Global constant from which the closure originates *)
}

let push_id ist id v = { env_ist = IdMap.add id v ist.env_ist }

let push_name ist id v = match id with
| Anonymous -> ist
| Name id -> push_id ist id v

let get_var ist id =
  try IdMap.find id ist.env_ist with Not_found ->
    anomaly (str "Unbound variable " ++ Id.print id)

let return = Proofview.tclUNIT

(** [bind_k m k]: [m >>= k], without the bind when [k] is [return] itself ([m >>= tclUNIT] is [m]),
    so that a tail call through it keeps no pending continuation, as [interp]'s tail calls keep
    none. *)
let bind_k m k = if k == return then m else m >>= k

exception NoMatch

let match_ctor_against ctor v =
  match ctor, v with
  | { cindx = Open ctor }, ValOpn (ctor', vs) ->
    if KerName.equal ctor ctor' then vs
    else raise NoMatch
  | { cindx = Open _ }, _ -> assert false
  | { cnargs = 0; cindx = Closed i }, ValInt i' ->
    if Int.equal i i' then [| |]
    else raise NoMatch
  | { cnargs = 0; cindx = Closed _ }, ValBlk _ -> raise NoMatch
  | _, ValInt _ -> raise NoMatch
  | { cindx = Closed i }, ValBlk (i', vs) ->
    if Int.equal i i' then vs
    else raise NoMatch
  | { cindx = Closed _ }, ValOpn _ -> assert false
  | _, (ValStr _ | ValCls _ | ValExt _) -> assert false

let check_atom_against atm v =
  match atm, v with
  | AtmInt n, ValInt n' -> if not (Int.equal n n') then raise NoMatch
  | AtmStr s, ValStr s' -> if not (String.equal s (Bytes.unsafe_to_string s')) then raise NoMatch
  | (AtmInt _ | AtmStr _), _ -> assert false

let rec match_pattern_against ist pat v =
  match pat with
  | GPatVar x -> push_name ist x v
  | GPatAtm atm -> check_atom_against atm v; ist
  | GPatAs (p,x) -> match_pattern_against (push_name ist (Name x) v) p v
  | GPatRef (ctor,pats) ->
    let vs = match_ctor_against ctor v in
    List.fold_left_i (fun i ist pat -> match_pattern_against ist pat vs.(i)) 0 ist pats
  | GPatOr pats -> match_pattern_against_or ist pats v

and match_pattern_against_or ist pats v =
  match pats with
  | [] -> raise NoMatch
  | pat :: pats ->
    try match_pattern_against ist pat v
    with NoMatch -> match_pattern_against_or ist pats v

let eval_glb_ext ist (Tac2dyn.Arg.Glb (tag,e)) =
  let tpe = Tac2env.interp_ml_object tag in
  with_frame (FrExtn (tag, e)) (tpe.Tac2env.ml_interp ist e)

(** The value of a global, computed once and reused where reuse cannot be observed.

    [eval_global] below computes the value of a global from three tables only: the compiled
    globals, the globals and, through [eval_pure]'s [GTacPrm] arm, the ML primitives. The value of
    a global is therefore the same as long as the three are the ones it was computed under, and
    computing it again is work that can be saved. On Igraph/RtLgTopA.v of the speed lane's fast
    set, [eval_global] was about 9% of the samples (dispatch://INFRA-217).

    Reusing a value is not the same as computing it again where Ltac2 code can write into the
    value or into a value it holds: [Valexpr.set_field] writes into the fields of any block
    (tac2val.ml:65-68), which the interpreter reaches through [GTacSet] (interp_set below) and
    Ltac2 code through "array_set", "array_blit" and "array_fill", whose implementations take the
    generic block (tac2core.ml:356-372, tac2ffi.ml:374-382), and "string_set" writes into the
    bytes of a [ValStr] (tac2core.ml:432-433). A primitive's declared Ltac2 type is not checked
    against its implementation (tac2entries.ml:472-488, [register_primitive]), so a user external
    declared at a permissive type reaches any block, not only an [Ltac2.Array]. So a value is
    reused only where it holds no block and no bytes at all: [shareable_value] below. *)
module GlobalValue :
sig
  val get : (bool -> ltac_constant -> valexpr) -> ltac_constant -> valexpr
  (** [get compute kn] is [compute keep kn], computed once while the tables are the ones it was
      computed under. [compute] must read those tables only and have no other effect. [keep]
      tells [compute] whether the value it gives will be kept and reused ([Shared] below); it
      must not change the value [compute] gives, only how that value is made (a function that is
      kept is worth compiling: [compiled_closure]). While a proof is recorded (BET-84) it is
      [compute false kn] at each use, because the reads [compute] makes are the proof's inputs. *)

  type cell
  (** A place in compiled code that reads one global ([compile_simple]). *)

  val cell : unit -> cell

  val get_cell : cell -> (bool -> ltac_constant -> valexpr) -> ltac_constant -> valexpr
  (** [get_cell c compute kn] is [get compute kn], for the global [kn] that [c] always reads. *)
end =
struct

(* [names] holds one entry per global, keyed by its name. A global's name is one object in each
   library that refers to it (unmarshalling copies it), and comparing two copies compares their
   strings: on Igraph/RtLgTopA.v that was 2.5% of the samples (dispatch://INFRA-217). So [copies]
   maps each name object met so far, by physical equality, to the entry of its name in [names]:
   a lookup compares strings only the first time it meets a copy. *)
module KNTbl = Hashtbl.Make(struct
  type t = KerName.t
  let equal kn1 kn2 = kn1 == kn2 || KerName.equal kn1 kn2
  let hash = KerName.hash
end)

module KNPhys = Hashtbl.Make(struct
  type t = KerName.t
  let equal kn1 kn2 = kn1 == kn2
  let hash = KerName.hash
end)

type entry =
| Shared of valexpr
  (** The value of the global. No evaluation can tell it from a value computed again. *)
| Recompute
  (** The global's value is computed at each use, as it holds, or may hold, a value Ltac2 code
      can write into. The entry saves deciding that again. *)

(** At most this many globals are kept. One input can define globals without end, and an entry
    holds its value and what the value holds; past the bound a global is computed at each use, as
    it was before this cache. The bound is far above what a development defines between two
    writes to the tables (Corelib's Ltac2 defines about a thousand globals), and 65536 entries of
    two words cost about 1 MB. [copies] holds at most [4 * bound] name objects, about 10 MB at
    worst: a copy past it is found in [names] at each use, as before [copies]. *)
let bound = 65536

let names : entry KNTbl.t = KNTbl.create 512

let copies : entry KNPhys.t = KNPhys.create 512

(** The tables the entries were computed under. Holding the two maps also keeps them alive, so no
    later map can be the same address as one of them and pass the test below. *)
let table_globals = ref (Tac2env.globals ())
let table_compiled = ref (Tac2env.compiled_globals ())
let table_primitives = ref (Tac2env.primitive_definitions ())

(** Whether [eval_pure] of [e], under bindings whose values are themselves shareable, gives a
    value that no Ltac2 code can tell from the value of a later evaluation of [e]: a value that is
    an immediate integer, or a closure, or the value of the primitive table, and that holds only
    such values.

    The arms follow [eval_pure]'s, and this descends only where [eval_pure] descends, so it ends
    wherever evaluating the global ends.

    - [GTacAtm (AtmInt _)] and a constructor without arguments ([GTacCst (_, _, [])]) give
      [ValInt], an immediate: there is nothing to write into.
    - [GTacFun] gives a closure over the bindings of the enclosing [GTacLet]s, which the arms
      below have checked. A closure holds no field Ltac2 code can write: [set_field] and the array
      primitives refuse anything but a block, and the environment a closure captures is read when
      the closure is called ([interp_closure]) and written only by [push_let_rec], on closures it
      has just built. Calling it evaluates its body, which allocates then, as calling a closure
      computed again would. Ltac2 has no equality on closures, so a shared closure is not visible.
    - [GTacVar] reads a binding of an enclosing [GTacLet], checked by the arms below.
    - [GTacPrm] gives the value of the primitive table. Every evaluation reads the same entry
      ([Tac2env.interp_primitive]), so evaluating it again gives that one value too, and reuse
      shares nothing new. [table_primitives] drops the entries where that table is written.
    - [GTacRef] gives the value of another global, shareable where that global's is.
    - [GTacLet] gives the value of its body, under values its bindings give. A binding of a
      recursive [GTacLet] is a closure ([push_let_rec]) over those same bindings. An anonymous
      non-recursive binding is not evaluated and binds nothing.
    - A string gives [ValStr], whose bytes "string_set" writes. [GTacCst] with arguments and
      [GTacOpn] with arguments give a block, whose fields [GTacSet] and the array primitives
      write. [GTacPrj] gives a field of a block, which is any value that block holds. The rest
      [eval_pure] refuses as not a syntactic value. *)
let rec shareable_value = function
| GTacAtm (AtmInt _) -> true
| GTacCst (_, _, []) -> true
| GTacFun _ -> true
| GTacVar _ -> true
| GTacPrm _ -> true
| GTacRef kn -> shareable_global kn
| GTacLet (false, bnd, body) ->
  List.for_all (fun (na, e) -> match na with Anonymous -> true | Name _ -> shareable_value e) bnd
  && shareable_value body
| GTacLet (true, bnd, body) ->
  List.for_all (fun (_, e) -> match e with GTacFun _ -> true | _ -> false) bnd
  && shareable_value body
| GTacAtm (AtmStr _) | GTacCst _ | GTacOpn _ | GTacPrj _
| GTacApp _ | GTacCse _ | GTacSet _ | GTacExt _ | GTacWth _ | GTacFullMatch _ -> false

(** Whether the value [eval_global] gives for [kn] is shareable. A compiled global's value is the
    one the table holds, which every evaluation returns, so reuse shares nothing new. *)
and shareable_global kn = match Tac2env.get_compiled_global kn with
| Some _ -> true
| None ->
  match Tac2env.interp_global kn with
  | exception Not_found -> false
  | { gdata_expr = e } -> shareable_value e

(** Incremented each time the entries are dropped below. Within one value of [epoch], an entry is
    added once per name and never changed or removed. *)
let epoch = ref 0

let check_tables () =
  let globals = Tac2env.globals () in
  let compiled = Tac2env.compiled_globals () in
  let primitives = Tac2env.primitive_definitions () in
  if globals != !table_globals || compiled != !table_compiled
     || not (Int.equal primitives !table_primitives)
  then begin
    KNTbl.reset names;
    KNPhys.reset copies;
    table_globals := globals;
    table_compiled := compiled;
    table_primitives := primitives;
    incr epoch
  end

(** The value [get] gives, and whether it is the value of a [Shared] entry (kept until [epoch]
    changes). Called after [check_tables]. [shareable_global] reads the tables only, which
    [compute] does not write, so asking it before [compute] gives what it gives after. *)
let get_entry compute kn =
  let entry =
    match KNPhys.find copies kn with
    | e -> Some e
    | exception Not_found ->
      let e = KNTbl.find_opt names kn in
      let () = match e with
      | Some e when KNPhys.length copies < 4 * bound -> KNPhys.add copies kn e
      | Some _ | None -> ()
      in
      e
  in
  match entry with
  | Some (Shared v) -> v, true
  | Some Recompute -> compute false kn, false
  | None ->
    let shared = shareable_global kn in
    let v = compute (shared && KNTbl.length names < bound) kn in
    if KNTbl.length names < bound then begin
      let e = if shared then Shared v else Recompute in
      KNTbl.replace names kn e;
      if KNPhys.length copies < 4 * bound then KNPhys.replace copies kn e;
      v, shared
    end
    else v, false

(* BET-84: a value taken from the entries skips the reads that computing it
   makes ([Tac2env.interp_global] and [record_global] on row 10, and the
   [ml_tactic] fence of [Tac2env.interp_primitive]), and the recorder must
   see each of them in each proof that uses the global, not only in the
   first one. So while a proof is recorded, each use computes the value
   again, as before this cache; [compute false] gives the same value. *)
let get compute kn =
  if Proof_recorder.active () then compute false kn
  else
    let () = check_tables () in
    fst (get_entry compute kn)

(** A cell keeps the value of a [Shared] entry and the [epoch] it was read in. While [epoch] has
    not changed, the tables are the ones the entry was computed under and the entry is still
    there, unchanged, so [get] would return that same value. *)
type cell = { mutable c_epoch : int; mutable c_value : valexpr }

let cell () = { c_epoch = -1; c_value = ValInt 0 }

let get_cell c compute kn =
  if Proof_recorder.active () then compute false kn
  else begin
    let () = check_tables () in
    if Int.equal c.c_epoch !epoch then c.c_value
    else
      let v, shared = get_entry compute kn in
      let () = if shared then begin c.c_epoch <- !epoch; c.c_value <- v end in
      v
  end

end
(** [simple_fuel fuel e]: [fuel] minus the number of nodes of [e] if [e] is an expression whose value
    [interp] computes without any effect (an atom, a variable, a global, a function, a primitive, or a
    constructor, open constructor or projection of such) and has at most [fuel] nodes; otherwise -1.
    [interp] returns [return v] on such an expression, with no bind, except under a constructor or
    projection, where it binds the values of the subexpressions in order. The node budget bounds the
    OCaml stack that [eval_simple] uses; stock's monadic path uses a near-constant stack, so a deeper
    expression (a long list literal, for example) takes that path. *)
let rec simple_fuel fuel e =
  if fuel <= 0 then -1
  else match e with
  | GTacAtm _ | GTacVar _ | GTacRef _ | GTacFun _ | GTacPrm _ -> fuel - 1
  | GTacCst (_, _, el) | GTacOpn (_, el) -> simple_fuel_list (fuel - 1) el
  | GTacPrj (_, e, _) -> simple_fuel (fuel - 1) e
  | GTacApp _ | GTacLet _ | GTacCse _ | GTacWth _ | GTacFullMatch _ | GTacSet _ | GTacExt _ -> -1

and simple_fuel_list fuel = function
  | [] -> fuel
  | e :: l -> let fuel = simple_fuel fuel e in if fuel < 0 then -1 else simple_fuel_list fuel l

(** At most this many nodes in all the arguments of one application go through [eval_simple]. *)
let max_simple_nodes = 64

let simple_args args = simple_fuel_list max_simple_nodes args >= 0

(** Compiled code (see "Compiled bodies" below): [scode] computes the value of a simple expression,
    [dcode] computes the value of an expression directly until a step needs the proof monad. *)
type scode = environment -> valexpr
type dcode = Tac2val.state -> int -> environment -> valexpr

(** The code of one expression: its direct code, and its value when it is simple. *)
type code = { d : dcode; s : scode option }

(** A compile-time scope: the identifiers that the newest bindings of the environment bind, newest
    first, each the very object that its binder binds; older bindings are not known. Compiled code
    reads a variable of the scope at its position ([compile_simple]), any other one by name. *)
type scope = Id.t list

let scope_push sc na = match na with
| Anonymous -> sc
| Name id -> id :: sc

let scope_pushes sc nas = List.fold_left scope_push sc nas

(** The position of [id] in [sc] and the object that binds it there. *)
let scope_find id sc =
  let rec find i = function
  | [] -> None
  | x :: l -> if Id.equal x id then Some (i, x) else find (i + 1) l
  in
  find 0 sc

(** [push_name] for compiled code: [IdMap.push], whose lookups give what [IdMap.add]'s give. *)
let cpush ist na v = match na with
| Anonymous -> ist
| Name id -> { env_ist = IdMap.push id v ist.env_ist }

(** [(cpush { env_ist = env } na v).env_ist]: one step of [push_args]. *)
let[@inline] push_arg env na v = match na with
| Anonymous -> env
| Name id -> IdMap.push id v env

(** [(List.fold_left2 cpush { env_ist = env } ids args).env_ist]. *)
let rec push_args env ids args = match ids, args with
| [], [] -> env
| Anonymous :: ids, _ :: args -> push_args env ids args
| Name id :: ids, v :: args -> push_args (IdMap.push id v env) ids args
| _ -> invalid_arg "List.fold_left2"

(** [CArray.fold_left2 cpush ist ids args], without the closure call per argument. *)
let cpush_array ist ids args =
  let len = Array.length ids in
  if not (Int.equal len (Array.length args)) then invalid_arg "Array.fold_left2";
  let rec push env i =
    if Int.equal i len then env
    else match Array.unsafe_get ids i with
    | Anonymous -> push env (i + 1)
    | Name id -> push (IdMap.push id (Array.unsafe_get args i) env) (i + 1)
  in
  { env_ist = push ist.env_ist 0 }

(** The scope after [match_pattern_against]'s bindings for [pat] (in its order), or nothing known
    if [pat] has an or-pattern, whose alternatives may bind in different orders. *)
let rec pattern_scope sc pat = match pat with
| GPatVar x -> Some (scope_push sc x)
| GPatAtm _ -> Some sc
| GPatAs (p, x) -> pattern_scope (scope_push sc (Name x)) p
| GPatRef (_, pats) ->
  List.fold_left (fun sc p -> match sc with None -> None | Some sc -> pattern_scope sc p) (Some sc) pats
| GPatOr _ -> None

(** [match_pattern_against] binding with [cpush]. *)
let rec cmatch_pattern ist pat v =
  match pat with
  | GPatVar x -> cpush ist x v
  | GPatAtm atm -> check_atom_against atm v; ist
  | GPatAs (p,x) -> cmatch_pattern (cpush ist (Name x) v) p v
  | GPatRef (ctor,pats) ->
    let vs = match_ctor_against ctor v in
    List.fold_left_i (fun i ist pat -> cmatch_pattern ist pat vs.(i)) 0 ist pats
  | GPatOr pats -> cmatch_pattern_or ist pats v

and cmatch_pattern_or ist pats v =
  match pats with
  | [] -> raise NoMatch
  | pat :: pats ->
    try cmatch_pattern ist pat v
    with NoMatch -> cmatch_pattern_or ist pats v

(** The compiled body of the functions made from one [GTacFun], compiled when one of them first
    runs, in [scope]: the scope of the body, with the function's arguments. *)
type code_cell = { mutable code : code option; scope : scope }

let code_cell scope = { code = None; scope }

(** At most this many nested calls of [compile_rt] in one compilation (see [compile_rt]). *)
let max_compile_depth = 256

let compile_depth = ref 0

(** At most this many nested evaluations of subexpressions not in tail position in one run of
    direct code (see "Compiled bodies" below). *)
let max_direct_depth = 512

(** [suspend s]: raise [Suspend s] (no backtrace: it is not an error). [tail t]: the same for
    [Tail t]. *)
let suspend s = raise_notrace (Suspend s)
let tail t = raise_notrace (Tail t)

(** [dk st f kk]: the direct code [f st] run with the continuation [kk]: its value [v] goes to
    [kk.ks v st] ([st] holds while direct code runs no step in the proof monad), its suspension
    [Suspend s] runs as [s kk], its tail step [Tail t] as [t kk.kv]. *)
let dk st f kk = match f st with
| v -> kk.ks v st
| exception Suspend s -> s kk
| exception Tail t -> t kk.kv

(** [resume s rest]: the suspension of a construct whose subexpression suspended with [s], [rest v
    st] the direct code of the rest of the construct on the subexpression's value [v]: [s] runs
    with a continuation that runs [rest] (with the state [s] gives, or none) and then the
    construct's own continuation [kk], which is passed on unchanged. *)
let resume s rest =
  suspend (fun kk -> s { kv = (fun v -> dk NoState (rest v) kk); ks = (fun v st -> dk st (rest v) kk) })

(** [dsub c st n ist]: the value of the subexpression [c], not in tail position, computed directly
    with [n] the depth left. Not in tail position, a tail step [Tail t] of [c] is the suspension
    that runs [t] with the value's continuation in a continuation of the proof monad, with nothing
    done in between: the same steps, on the proof monad's stack. At depth 0 the direct code of
    [c] runs so too, with the whole depth. *)
let dsub_deep c st ist =
  suspend (fun kk -> return () >>= fun () -> dk st (fun st -> c.d st max_direct_depth ist) kk)

let dsub_tail t = suspend (fun kk -> return () >>= fun () -> t kk.kv)

let[@inline] dsub c st n ist = match c.s with
| Some s -> s ist
| None ->
  if n > 0 then (match c.d st (n - 1) ist with v -> v | exception Tail t -> dsub_tail t)
  else dsub_deep c st ist

let rec interp (ist : environment) = function
| GTacAtm (AtmInt n) -> return (Tac2ffi.of_int n)
| GTacAtm (AtmStr s) -> return (Tac2ffi.of_string s)
| GTacVar id -> return (get_var ist id)
| GTacRef kn -> return (eval_global kn)
| GTacFun (ids, e) ->
  let cls = { clos_ref = None; clos_env = ist.env_ist; clos_var = ids; clos_exp = e } in
  let f = interp_closure cls in
  return f
| GTacApp (f, args) ->
  interp ist f >>= fun f ->
  (* Arguments that are all simple are evaluated here, in one step. This gives what the general path
     gives: [Proofview.Monad.List.map] evaluates the first argument here and each next one in the
     continuation of the previous one's [return], which has exactly one success, so each of those
     continuations runs once each time this one does, with no effect in between. On
     Igraph/RtLgTopA.v the binds and returns of the proof monad were 22.8% of the samples. *)
  if simple_args args then apply_tail f (eval_simple_list ist args)
  else args_rt ist [] args (fun args -> apply_tail f args)
| GTacLet (false, (na, e1) :: el, e) ->
  (* [interp ist e1 >>= fun v -> return (push_name ist na v)] is the first step of the fold below;
     its continuation and every later step run at run time ([let_rt]). *)
  bind_ct ist e1 (fun v -> let_rt ist (push_name ist na v) el (fun accu -> interp_rt accu e))
| GTacLet (false, el, e) ->
  let fold accu (na, e) =
    interp ist e >>= fun e ->
    return (push_name accu na e)
  in
  Proofview.Monad.List.fold_left fold ist el >>= fun ist ->
  interp ist e
| GTacLet (true, el, e) ->
  let ist = push_let_rec ist.env_ist el in
  interp { env_ist = ist } e
| GTacCst (_, n, []) -> return (Valexpr.make_int n)
| GTacCst (_, n, el) ->
  Proofview.Monad.List.map (fun e -> interp ist e) el >>= fun el ->
  return (Valexpr.make_block n (Array.of_list el))
| GTacCse (e, _, cse0, cse1) ->
  bind_ct ist e (fun e -> interp_case ist e cse0 cse1)
| GTacWth { opn_match = e; opn_branch = cse; opn_default = def } ->
  interp ist e >>= fun e -> interp_with ist e cse def
| GTacFullMatch (e,brs) ->
  interp ist e >>= fun e -> interp_full_match ist e brs
| GTacPrj (_, e, p) ->
  interp ist e >>= fun e -> interp_proj ist e p
| GTacSet (_, e, p, r) ->
  interp ist e >>= fun e ->
  interp ist r >>= fun r ->
  interp_set ist e p r
| GTacOpn (kn, el) ->
  Proofview.Monad.List.map (fun e -> interp ist e) el >>= fun el ->
  return (Tac2ffi.of_open (kn, Array.of_list el))
| GTacPrm ml ->
  return (Tac2env.interp_primitive ml)
| GTacExt (tag, e) -> eval_glb_ext ist (Glb (tag,e))

and push_let_rec ist el = push_let_rec_with IdMap.add (fun _ cls -> interp_closure cls) ist el

(** [push_let_rec_with add mk ist el] is [push_let_rec ist el] with the bindings made by [add]
    ([IdMap.add] or [IdMap.push], whose lookups give the same) and the function of the [i]-th
    binding made by [mk i]. *)
and push_let_rec_with add mk ist el =
  let map i (na, e) = match e with
  | GTacFun (ids, e) ->
    let cls = { clos_ref = None; clos_env = ist; clos_var = ids; clos_exp = e } in
    let f = mk i cls in
    na, cls, f
  | _ -> anomaly (str "Ill-formed recursive function")
  in
  let fixs = List.mapi map el in
  let fold accu (na, _, cls) =match na with
    | Anonymous -> accu
    | Name id -> add id cls accu
  in
  let ist = List.fold_left fold ist fixs in
  (* Hack to make a cycle imperatively in the environment *)
  let iter (_, e, _) = e.clos_env <- ist in
  let () = List.iter iter fixs in
  ist

(** The function of [f] whose body runs as [bind_rt]. Its direct run computes nothing directly: its
    body is the tail step [bind_rt ist f.clos_exp k]. *)
and interp_closure f =
  closure_value (fun env ids args -> List.fold_left2 push_name { env_ist = env } ids args)
    (fun _ -> NoFast) f
    (fun ist k -> bind_rt ist f.clos_exp k)
    (fun _ _ ist -> tail (fun k -> bind_rt ist f.clos_exp k))

(** The function of [f] whose body, when it runs directly, is [f]'s compiled body, kept in
    [cell] (see "Compiled bodies" below); its arguments are then bound with [IdMap.push], in the
    order of [cell.scope]. The body runs as direct code ([enter], "Compiled bodies" below). It
    carries the [Tac2val.fast] entry of its number of arguments, up to 5: [compiled_fast]. *)
and compiled_closure f cell =
  closure_value (fun env ids args -> { env_ist = push_args env ids args }) (compiled_fast f cell) f
    (fun ist k -> enter (body_code cell f.clos_exp) ist k)
    (fun st n ist -> (body_code cell f.clos_exp).d st n ist)

(** [compiled_fast f cell ans]: the [fast] entry of [compiled_closure f cell], whose [ans] (see
    [closure_value]) is [ans]. On [k] arguments it is [drun st n [a1; ...; ak]] ([closure_value]):
    the same test, then the arguments bound one by one by [push_arg] in the order of [f.clos_var]
    (an immutable field, so read here once), as [push_args] binds them, on [f.clos_env] read at
    the call, and the compiled body run directly; otherwise the tail step [ans args >>= k]. *)
and compiled_fast f cell ans = match f.clos_var with
| [i1] ->
  Run1 (fun st n a ->
    if Tac2bt.with_frame_is_identity () then
      let env = push_arg f.clos_env i1 a in
      (body_code cell f.clos_exp).d st n { env_ist = env }
    else tail (fun k -> ans [a] >>= k))
| [i1; i2] ->
  Run2 (fun st n a b ->
    if Tac2bt.with_frame_is_identity () then
      let env = push_arg (push_arg f.clos_env i1 a) i2 b in
      (body_code cell f.clos_exp).d st n { env_ist = env }
    else tail (fun k -> ans [a; b] >>= k))
| [i1; i2; i3] ->
  Run3 (fun st n a b c ->
    if Tac2bt.with_frame_is_identity () then
      let env = push_arg (push_arg (push_arg f.clos_env i1 a) i2 b) i3 c in
      (body_code cell f.clos_exp).d st n { env_ist = env }
    else tail (fun k -> ans [a; b; c] >>= k))
| [i1; i2; i3; i4] ->
  Run4 (fun st n a b c d ->
    if Tac2bt.with_frame_is_identity () then
      let env = push_arg (push_arg (push_arg (push_arg f.clos_env i1 a) i2 b) i3 c) i4 d in
      (body_code cell f.clos_exp).d st n { env_ist = env }
    else tail (fun k -> ans [a; b; c; d] >>= k))
| [i1; i2; i3; i4; i5] ->
  Run5 (fun st n a b c d e ->
    if Tac2bt.with_frame_is_identity () then
      let env = push_arg (push_arg (push_arg (push_arg (push_arg f.clos_env i1 a) i2 b) i3 c) i4 d) i5 e in
      (body_code cell f.clos_exp).d st n { env_ist = env }
    else tail (fun k -> ans [a; b; c; d; e] >>= k))
| _ -> NoFast

(** [closure_value bind fast f body dbody]: the value of the function [f], whose body runs at run
    time as [body ist k] ([bind_rt ist f.clos_exp k], or the same compiled), and directly as [dbody
    st n ist] (see "Compiled bodies" below), its arguments bound by [bind] ([push_name] or
    [IdMap.push] over the arguments, whose environments give the same lookups). It carries the
    entry [fast ans] ([Tac2val.fast]), which must agree with [drun] below. *)
and closure_value bind fast f body dbody =
  let ans = fun args ->
    let { clos_env = ist; clos_var = ids; clos_exp = e; clos_ref = kn } = f in
    let frame = match kn with
    | None -> FrAnon e
    | Some kn -> FrLtac kn
    in
    let ist = { env_ist = ist } in
    let ist = List.fold_left2 push_name ist ids args in
    with_frame frame (interp ist e)
  in
  (* [run args k] is [ans args >>= k] when it is called at run time ([Tac2val.DirectRun]): [ans]
     reads the closure's fields and binds its arguments when it is applied, as [run] does, and then
     builds the body's tactic under [with_frame], which is the identity on it exactly when
     [with_frame_is_identity ()] holds at that moment (both flags, the backtrace and Ltac2-in-Ltac1
     profiling, as [with_frame] reads them; only the first has an output test, as profile output
     prints times); at run time the body is run at once by [body] (see Run time below). *)
  let run args k =
    if Tac2bt.with_frame_is_identity () then
      let { clos_env = ist; clos_var = ids; clos_exp = _; clos_ref = _ } = f in
      body (bind ist ids args) k
    else ans args >>= k
  in
  (* [drun st n args] is [run args k] up to its first step in the proof monad (Tac2val.DirectRun):
     the same test and the same binding, then [dbody], whose value, [Suspend] or [Tail] is that of
     [body] ([dcode] below); otherwise [run args k] is the tail step [ans args >>= k]. *)
  let drun st n args =
    if Tac2bt.with_frame_is_identity () then
      let { clos_env = ist; clos_var = ids; clos_exp = _; clos_ref = _ } = f in
      dbody st n (bind ist ids args)
    else tail (fun k -> ans args >>= k)
  in
  Tac2ffi.of_closure (Tac2val.abstract_run ~fast:(fast ans) (List.length f.clos_var) ans run drun)

(** [interp_case] runs at run time only: in the continuation of the scrutinee's value. *)
and interp_case ist e cse0 cse1 = case_rt ist e cse0 cse1 interp_rt

(** [case_rt ist e cse0 cse1 fin], at run time: [fin ist' br] for the branch [br] of the value [e],
    [ist'] binding the arguments of its constructor. *)
and case_rt ist e cse0 cse1 fin =
  if Valexpr.is_int e then
    fin ist cse0.(Tac2ffi.to_int e)
  else
    let (n, args) = Tac2ffi.to_block e in
    let (ids, e) = cse1.(n) in
    let ist = CArray.fold_left2 push_name ist ids args in
    fin ist e

(** {6 Run time}

    [interp ist e] builds a tactic: the arms above compute some values when they are called (a
    variable, a global, a closure) and bind the rest. Where [interp] is called matters. A tactic can
    be built once and run several times: [Control.enter] builds the body of its closure once and
    runs that tactic in each goal ([Proofview.tclINDEPENDENT], tac2core.ml "enter"). And a handler
    can cover the building of a tactic but not its run: [Proofview.Goal.enter] turns an exception
    raised while building into a failure of the tactic. So a value that stock computes when the
    tactic runs must not be computed when it is built, and the arms above build what stock builds.

    The functions below ([*_rt], [bind_rt], [apply_bind], [apply_tail], [args_rt], [let_rt],
    [case_rt], [interp_case], and the [run] of [interp_closure]) are called only at run time: in
    the continuation of a bind, or from another of them. There, building a tactic and running it
    are one step: a continuation's tactic is built and run at once, every time the continuation
    runs. So the values that stock computes in a chain of [return v >>= k] are computed here
    directly, in the same order, and passed to the OCaml continuation [k]. [return v >>= k] runs
    [k v] once, with no effect in between, each time it runs; [Logic_monad.Logical]'s [return]
    and [bind] install no exception handler, so a computation that raises raises through the same
    handlers in both. Bind is associative, so [(m >>= f) >>= k] is [m >>= fun v -> f v >>= k]:
    [bind_rt] passes [k] on to the last step of a call, a let or a match. So the values, the
    effects and their order, the run counts under backtracking, the exceptions and the proof state
    are stock's. The binds left out are those of [return] only: every primitive with an effect,
    and every construct but variables, constants, functions, constructors and projections of
    them, calls, lets and matches, still goes through the proof monad as in stock.

    A pure primitive ([Tac2val.closure_direct]) applied to exactly as many arguments as it takes
    is, in stock, [tclUNIT () >>= fun () -> tclUNIT (f args)] (or reads the environment and the
    evar map first, [DirectEnv]); at run time [f args] is computed directly. An Ltac2 closure
    applied to exactly as many arguments as it takes is, in stock, the tactic that [interp] builds
    of its body (when [with_frame] adds nothing, [DirectRun]); at run time the body is run at once
    with [bind_rt].

    OCaml stack: chains of calls, lets, arguments and branches are tail calls, so a recursive Ltac2
    function runs in constant stack, its pending work in the continuations; the fallback of
    [bind_rt] ([interp_rt ist e >>= k]) is not, so a nest of other constructs uses stack in
    proportion to its depth, as internalization of the same expression does. *)

(** [bind_ct ist e k]: the tactic [interp ist e >>= k], built at construction time. [k] runs only
    in a continuation. *)
and bind_ct ist e k = match e with
| GTacApp (f, args) when simple_args args ->
  (* [interp ist (GTacApp (f, args))] binds [interp ist f] to [apply_val f (eval_simple_list ist
     args)]; [>>= k] associates into its continuation. *)
  interp ist f >>= fun f -> apply_bind f (eval_simple_list ist args) k
| _ -> interp ist e >>= k

(** [bind_rt ist e k], at run time: [interp ist e >>= k]. A call, a let and a match pass [k] on
    to the step that ends them (associativity of bind): the call itself, the body of the let, the
    branch of the match. *)
and bind_rt ist e k =
  if simple_fuel max_simple_nodes e >= 0 then k (eval_simple ist e)
  else match e with
  | GTacApp (f, args) when simple_fuel max_simple_nodes f >= 0 ->
    let f = eval_simple ist f in
    if simple_args args then apply_bind f (eval_simple_list ist args) k
    else args_rt ist [] args (fun args -> apply_bind f args k)
  | GTacLet (false, el, e) -> let_rt ist ist el (fun accu -> bind_rt accu e k)
  | GTacCse (e, _, cse0, cse1) ->
    bind_rt ist e (fun e -> case_rt ist e cse0 cse1 (fun ist e -> bind_rt ist e k))
  | _ -> bind_k (interp_rt ist e) k

(** [apply_val_bind f args k]: [Tac2val.apply_val f args >>= k] ([bind_k]). *)
and apply_val_bind f args k = bind_k (Tac2val.apply_val f args) k

(** [apply_bind f args k], at run time: [Tac2val.apply_val f args >>= k]. *)
and apply_bind f args k = apply_bind_n (List.length args) f args k

(** [apply_bind_n n f args k] is [apply_bind f args k] for [args] of length [n]. A primitive with a
    check ([DirectCheck]) whose check gives [v] is [tclUNIT () >>= fun () -> tclUNIT v], and [>>= k]
    of it is [k v]. A function given fewer arguments than it takes is [tclUNIT] of the value that
    [apply_partial_val] computes by the same steps, and [>>= k] of it is [k] of that value. *)
and apply_bind_n nargs f args k = match Tac2val.closure_direct f with
| Some (DirectPure (n, d)) when Int.equal n nargs -> k (d args)
| Some (DirectEnv (n, d)) when Int.equal n nargs ->
  let d = d args in
  Proofview.tclENV >>= fun env -> Proofview.tclEVARMAP >>= fun sigma -> k (d env sigma)
| Some (DirectRun (n, d, _)) when Int.equal n nargs -> d args k
| Some (DirectCheck (n, c)) when Int.equal n nargs ->
  begin match c args with
  | Some v -> k v
  | None -> apply_val_bind f args k
  end
| Some (DirectPure (n, _) | DirectEnv (n, _) | DirectRun (n, _, _) | DirectCheck (n, _)) when nargs < n ->
  k (Tac2val.apply_partial_val f args)
| Some (DirectPure _ | DirectEnv _ | DirectRun _ | DirectCheck _) | None -> apply_val_bind f args k

(** [apply_tail f args], at run time: [Tac2val.apply_val f args], which is
    [Tac2val.apply_val f args >>= return]. *)
and apply_tail f args = match Tac2val.closure_direct f with
| Some (DirectPure (n, d)) when Int.equal n (List.length args) -> return (d args)
| Some (DirectEnv (n, d)) when Int.equal n (List.length args) ->
  let d = d args in
  Proofview.tclENV >>= fun env -> Proofview.tclEVARMAP >>= fun sigma -> return (d env sigma)
| Some (DirectRun (n, d, _)) when Int.equal n (List.length args) -> d args return
| Some (DirectCheck (n, c)) when Int.equal n (List.length args) ->
  begin match c args with
  | Some v -> return v
  | None -> Tac2val.apply_val f args
  end
| Some (DirectPure (n, _) | DirectEnv (n, _) | DirectRun (n, _, _) | DirectCheck (n, _))
  when List.length args < n ->
  return (Tac2val.apply_partial_val f args)
| Some (DirectPure _ | DirectEnv _ | DirectRun _ | DirectCheck _) | None -> Tac2val.apply_val f args

(** [args_rt ist acc args k], at run time: [Proofview.Monad.List.map (interp ist) args >>= fun l ->
    k (List.rev_append acc l)], the arguments from left to right. *)
and args_rt ist acc args k = match args with
| [] -> k (List.rev acc)
| e :: args -> bind_rt ist e (fun v -> args_rt ist (v :: acc) args k)

(** [let_rt ist accu el fin], at run time: the fold of [GTacLet (false, _, e)]'s arm over [el] from
    the accumulated environment [accu], then [fin] on the environment it gives ([interp_rt _ e],
    or [bind_rt _ e k]). The right-hand sides are evaluated in [ist]. *)
and let_rt ist accu el fin = match el with
| [] -> fin accu
| (na, e') :: el -> bind_rt ist e' (fun v -> let_rt ist (push_name accu na v) el fin)

(** [interp_rt ist e], at run time: [interp ist e]. *)
and interp_rt ist e =
  if simple_fuel max_simple_nodes e >= 0 then return (eval_simple ist e)
  else match e with
  | GTacApp (f, args) when simple_fuel max_simple_nodes f >= 0 ->
    let f = eval_simple ist f in
    if simple_args args then apply_tail f (eval_simple_list ist args)
    else args_rt ist [] args (fun args -> apply_tail f args)
  | GTacLet (false, el, e) -> let_rt ist ist el (fun accu -> interp_rt accu e)
  | GTacCse (e, _, cse0, cse1) -> bind_rt ist e (fun e -> interp_case ist e cse0 cse1)
  | _ -> interp ist e

and interp_with ist e cse def =
  let (kn, args) = Tac2ffi.to_open e in
  let br = try Some (KerName.Map.find kn cse) with Not_found -> None in
  begin match br with
  | None ->
    let (self, def) = def in
    let ist = push_name ist self e in
    interp ist def
  | Some (self, ids, p) ->
    let ist = push_name ist self e in
    let ist = CArray.fold_left2 push_name ist ids args in
    interp ist p
  end

and interp_full_match ist e = function
  | [] -> CErrors.anomaly Pp.(str "ltac2 match not exhaustive")
  | (pat,br) :: rest ->
    begin match match_pattern_against ist pat e with
    | exception NoMatch -> interp_full_match ist e rest
    | ist -> interp ist br
    end

and interp_proj ist e p =
  return (Valexpr.field e p)

and interp_set ist e p r =
  let () = Valexpr.set_field e p r in
  return (Valexpr.make_int 0)

and eval_global kn = GlobalValue.get compute_global kn

(** [keep]: the value is kept and reused ([GlobalValue.get]); its functions are then made with
    compiled bodies ([eval_pure]), which [compute_global] makes once per global instead of at
    each use. *)
and compute_global keep kn =
  match Tac2env.get_compiled_global kn with
  | Some (_info,v) ->
    let () =
      if Proof_recorder.active () then Tac2env.record_global kn
    in
    v
  | None -> match Tac2env.interp_global kn with
    | exception Not_found -> anomaly (str "Unbound reference" ++ KerName.print kn)
    | { gdata_expr = e } -> eval_pure keep IdMap.empty (Some kn) e

(** [eval_pure comp bnd kn e]: the value of the syntactic value [e]. With [comp], the functions it
    makes have compiled bodies ([compiled_closure]); they are the same functions. *)
and eval_pure comp bnd kn = function
| GTacVar id -> IdMap.get id bnd
| GTacAtm (AtmInt n) -> Valexpr.make_int n
| GTacRef kn -> eval_global kn
| GTacFun (na, e) ->
  let cls = { clos_ref = kn; clos_env = bnd; clos_var = na; clos_exp = e } in
  if comp then compiled_closure cls (code_cell (scope_pushes [] na)) else interp_closure cls
| GTacCst (_, n, []) -> Valexpr.make_int n
| GTacCst (_, n, el) -> Valexpr.make_block n (eval_pure_args comp bnd el)
| GTacOpn (kn, el) -> Tac2ffi.of_open (kn, eval_pure_args comp bnd el)
| GTacLet (false, vals, body) ->
  let fold accu (na, e) = match na with
  | Anonymous ->
    (* No need to evaluate, we know this is a value *)
    accu
  | Name id ->
    let v = eval_pure comp bnd None e in
    IdMap.add id v accu
  in
  let bnd = List.fold_left fold bnd vals in
  eval_pure comp bnd kn body
| GTacLet (true, el, body) ->
  let bnd =
    if comp then
      let sc = scope_pushes [] (List.map fst el) in
      push_let_rec_with IdMap.push
        (fun _ cls -> compiled_closure cls (code_cell (scope_pushes sc cls.clos_var))) bnd el
    else push_let_rec bnd el
  in
  eval_pure comp bnd kn body
| GTacPrj (_,e,i) ->
  let v = eval_pure comp bnd kn e in
  Valexpr.field v i

| GTacPrm ml -> Tac2env.interp_primitive ml

| GTacAtm (AtmStr _) | GTacSet _
| GTacApp _ | GTacCse _
| GTacExt _ | GTacWth _
| GTacFullMatch _ ->
  anomaly (Pp.str "Term is not a syntactical value")

and eval_pure_args comp bnd args =
  let map e = eval_pure comp bnd None e in
  Array.map_of_list map args

(** [eval_simple ist e], [e] simple ([simple_fuel]): the value that [interp ist e] returns, computed
    directly. The subexpressions of a constructor are evaluated from left to right, as
    [Proofview.Monad.List.map] does. *)
and eval_simple ist = function
| GTacAtm (AtmInt n) -> Tac2ffi.of_int n
| GTacAtm (AtmStr s) -> Tac2ffi.of_string s
| GTacVar id -> get_var ist id
| GTacRef kn -> eval_global kn
| GTacFun (ids, e) ->
  interp_closure { clos_ref = None; clos_env = ist.env_ist; clos_var = ids; clos_exp = e }
| GTacPrm ml -> Tac2env.interp_primitive ml
| GTacCst (_, n, []) -> Valexpr.make_int n
| GTacCst (_, n, el) -> Valexpr.make_block n (Array.of_list (eval_simple_list ist el))
| GTacOpn (kn, el) -> Tac2ffi.of_open (kn, Array.of_list (eval_simple_list ist el))
| GTacPrj (_, e, p) -> Valexpr.field (eval_simple ist e) p
| GTacApp _ | GTacLet _ | GTacCse _ | GTacWth _ | GTacFullMatch _ | GTacSet _ | GTacExt _ ->
  anomaly (Pp.str "Term is not simple")

(* left to right, explicitly *)
and eval_simple_list ist = function
| [] -> []
| e :: l -> let v = eval_simple ist e in v :: eval_simple_list ist l

(** {6 Compiled bodies}

    [compile_rt sc e] compiles [e] once into OCaml code, its direct code [d] (and its value [s] when
    [e] is simple, [simple_fuel]). Every decision that depends on [e] alone is taken then: whether
    it is simple and which node it is. What depends on values (the function applied, its direct
    implementation and arity, the branch taken, the value of a global) is decided when the code
    runs, by the same functions as [bind_rt] ([GlobalValue], [Tac2val.closure_direct]). Compiling
    reads [e] and allocates; it has no other effect, so when it happens cannot be observed.

    The direct code [c.d st n ist] of [e] compiled as [c] runs the steps that [bind_rt ist e k],
    that is [interp ist e >>= k] at run time (Run time above), runs before it gives [k] a value or
    does a step in the proof monad. Then it returns that value [v], where [bind_rt ist e k] runs [k
    v], or raises [Suspend s], where it runs [s kk] for any continuation [kk] ([Tac2val.cont])
    whose [kk.kv v] and [kk.ks v st] are [k v] (for [st] the state at that moment, or [NoState]),
    or, when that step ends [e] (a tail step), raises [Tail t], where it runs [t k]. Any other
    exception it raises, [bind_rt ist e k] raises after the same steps. [st] is the environment
    and the evar map of the proof state at that moment when they are known ([Tac2val.state]), [n]
    the depth left; [s] gives [kk.ks] the state at the moment it gives the value, when known. So
    the pure steps (building values, binding variables, matching, writing fields, pure primitives,
    calls) are done directly, without the proof monad's binds and without allocating continuations.
    On Igraph/RtLgTopA.v, 185 million Ltac2 calls ran in compiled bodies, and the continuations and
    binds were most of their cost (dispatch://INFRA-217).

    This holds by induction on the expression, arm by arm of [compile_node] against [interp]'s,
    with [return v >>= k] = [k v] and associativity of bind (no handler is moved, nothing runs in
    between: Run time above):
    - A simple expression: [interp] returns [eval_simple ist e], which is [s ist].
    - A call: [interp ist f], then the arguments by [Proofview.Monad.List.map] from left to right,
      then [apply_val]; the direct code computes them in that order, those not in tail position
      with [dsub], and [dapply] applies the function as [apply_val _ _ >>= k] does (see there).
    - A let (its right-hand sides in [ist], then the body), a match on a closed type, a constructor,
      an open constructor, a projection, a write, a full match, a match on an open type and a
      recursive let of functions: [interp]'s arm, with its pure steps (building the value, matching
      the patterns, writing the field, making the recursive functions, binding the variables with
      [cpush], whose lookups give [push_name]'s) in the same order, the subexpressions not in tail
      position with [dsub] and the body or branch in tail position.
    - If a subexpression raises [Suspend s], [interp] runs, after the same steps, the
      subexpression's step and then, in its continuation, the rest of the construct with [k]. The
      direct code raises [resume s rest], [rest] the direct code of that same rest: [s] runs with
      the continuation that runs [rest] by [dk] and passes the construct's continuation [kk] on.
      By induction [rest] does the same steps as [interp]'s rest and ends in the same value,
      suspension or tail step, which [dk] gives to [kk] as [enter] gives them to [k]. The rest
      runs with the state [s] gave, or [NoState]. Because [kk] is passed on unchanged, a tail step
      in the rest gets [enter]'s own [k]: a loop of tail calls keeps no pending continuation.
    - A call whose function has no direct implementation for these arguments, and the other
      expressions (extension nodes, [GTacExt]), are tail steps: [Tail (fun k -> apply_val f args
      >>= k)], [Tail (fun k -> interp ist e >>= k)] (with no bind when [k] is [return]: [bind_k]).
      [t k] builds the tactic when it is called:
      right after the direct code returns to [enter] or [dk], with nothing in between.
    - [dsub] turns a tail step [Tail t] of a subexpression, which is not in tail position there,
      into a suspension that runs [t kk.kv], and at depth 0 it raises a suspension that runs the
      direct code of the subexpression with [dk], each in a continuation of [return ()]: the same
      steps, with nothing in between, as the proof monad runs that continuation at once.

    [st] holds the proof state's environment and evar map whenever it is [State]: only [dapply]
    makes it, from [tclENV] and [tclEVARMAP], and it holds while direct code runs no step in the
    proof monad: only those change the proof state, and each of them is a suspension, after which
    the state is the one its tactic gives.

    So, under backtracking, the steps before a suspension run once, as in [interp], where they come
    before its first step in the proof monad, and the rest runs in the continuation of that step,
    once per success of it, as in [interp]. The direct code catches [Suspend] and [Tail] only,
    which only direct code raises, so other exceptions pass as in [interp]. A function's direct run checks
    [Tac2bt.with_frame_is_identity] as [run] does ([closure_value]). Stack: a call in tail position
    is an OCaml tail call, and each subexpression not in tail position takes one from [n]; [n]
    starts at [max_direct_depth] in [enter] and in each continuation of a suspension. A step in the
    proof monad is not run on the direct code's stack: the direct code raises it, and it runs
    after the stack is unwound, in [enter] or [dk] (as an OCaml tail call) or in the proof monad's
    continuation. So the stack of direct code is bounded by [max_direct_depth] nested
    subexpressions, and a loop of tail calls through steps in the proof monad keeps, as in
    [interp], no pending continuation ([apply_val_bind]).

    Direct code runs only where [bind_rt] may run: in [closure_value]'s [run] and [drun], at run
    time. Functions made by compiled code (a [GTacFun], a recursive let) are [compiled_closure]s
    with one [code_cell] per [GTacFun] node: every function made from that node runs the one
    compiled body, compiled when one of them first runs; each has its own environment, read when it
    is applied, as in [closure_value]. A global read by compiled code goes through one
    [GlobalValue.cell] per [GTacRef] node ([GlobalValue.get_cell] is [GlobalValue.get]). As in
    [eval_simple], strings, integers and constructors are made anew at each evaluation. *)

and body_code cell e = match cell.code with
| Some c -> c
| None ->
  let c = compile_rt cell.scope e in
  let () = cell.code <- Some c in
  c

(** [compile_rt sc e]: [e] compiled in the scope [sc]; the code binds variables with [cpush] in the
    order of [sc]'s extensions, as [interp] binds them with [push_name].

    Compiling recurses on the expression, and [body_code] compiles at run time, on the stack the
    running tactic already uses, where stock runs the same body in near-constant stack (Run time
    above). So a subexpression deeper than [max_compile_depth] nested compiles is not compiled: its
    direct code raises the tail step [bind_rt ist e k]. [bind_rt]
    reads variables by name and binds with [IdMap.add], whose lookups give what [IdMap.push]'s
    give, so the environment compiled code made serves it as is, and what it binds stays in its own
    continuations: the compiled code after it reads the environment it closed over. Compiling never
    runs code, so [compile_depth] counts the nested calls of one compilation only; it is back to 0
    when [compile_rt] returns or raises. *)
and compile_rt sc e : code =
  if !compile_depth >= max_compile_depth then
    { d = (fun _ _ ist -> tail (fun k -> bind_rt ist e k)); s = None }
  else begin
    incr compile_depth;
    match compile_node sc e with
    | c -> decr compile_depth; c
    | exception ex -> let ex = Exninfo.capture ex in decr compile_depth; Exninfo.iraise ex
  end

and compile_node sc e : code =
  if simple_fuel max_simple_nodes e >= 0 then
    let s = compile_simple sc e in
    { d = (fun _ _ ist -> s ist); s = Some s }
  else match e with
  | GTacApp (f, args) when simple_fuel max_simple_nodes f >= 0 && simple_args args ->
    (* The function and the arguments are simple: [call_simple]'s steps, after [f]'s value. *)
    let f = compile_simple sc f in
    let nargs = List.length args in
    begin match List.map (compile_simple sc) args with
    | [a1] -> { d = (fun st n ist -> let fv = f ist in let x1 = a1 ist in dapply1 st n fv x1); s = None }
    | [a1; a2] ->
      { d = (fun st n ist ->
          let fv = f ist in let x1 = a1 ist in let x2 = a2 ist in dapply2 st n fv x1 x2);
        s = None }
    | [a1; a2; a3] ->
      { d = (fun st n ist ->
          let fv = f ist in let x1 = a1 ist in let x2 = a2 ist in let x3 = a3 ist in
          dapply3 st n fv x1 x2 x3);
        s = None }
    | [a1; a2; a3; a4] ->
      { d = (fun st n ist ->
          let fv = f ist in let x1 = a1 ist in let x2 = a2 ist in let x3 = a3 ist in
          let x4 = a4 ist in
          dapply4 st n fv x1 x2 x3 x4);
        s = None }
    | [a1; a2; a3; a4; a5] ->
      { d = (fun st n ist ->
          let fv = f ist in let x1 = a1 ist in let x2 = a2 ist in let x3 = a3 ist in
          let x4 = a4 ist in let x5 = a5 ist in
          dapply5 st n fv x1 x2 x3 x4 x5);
        s = None }
    | _ ->
      let args = compile_simple_list sc args in
      { d = (fun st n ist -> let fv = f ist in dapply st n nargs fv (args ist)); s = None }
    end
  | GTacApp (f, args) ->
    let call = if simple_args args then call_simple sc args else call_args sc args in
    if simple_fuel max_simple_nodes f >= 0 then
      let f = compile_simple sc f in
      { d = (fun st n ist -> let f = f ist in call st n ist f); s = None }
    else
      let f = compile_rt sc f in
      { d = (fun st n ist ->
          let fv = match dsub f st n ist with
          | fv -> fv
          | exception Suspend s ->
            resume s (fun fv st -> call st max_direct_depth ist fv)
          in
          call st n ist fv);
        s = None }
  | GTacLet (false, [(na, e1)], body) ->
    (* [dlet] on one binding: its value, then the body on [cpush ist na v]. *)
    let e1 = compile_rt sc e1 in
    let body = compile_rt (scope_push sc na) body in
    { d = (fun st n ist ->
        let v = match dsub e1 st n ist with
        | v -> v
        | exception Suspend s ->
          resume s (fun v st -> body.d st max_direct_depth (cpush ist na v))
        in
        body.d st n (cpush ist na v));
      s = None }
  | GTacLet (false, el, body) ->
    let el = List.map (fun (na, e) -> (na, compile_rt sc e)) el in
    let body = compile_rt (scope_pushes sc (List.map fst el)) body in
    { d = (fun st n ist -> body.d st n (dlet st n ist ist el body)); s = None }
  | GTacLet (true, el, body)
    when List.for_all (fun (_, e) -> match e with GTacFun _ -> true | _ -> false) el ->
    let sc = scope_pushes sc (List.map fst el) in
    let cells = Array.of_list (List.map (fun (_, e) -> match e with
      | GTacFun (ids, _) -> code_cell (scope_pushes sc ids)
      | _ -> assert false) el)
    in
    let body = compile_rt sc body in
    let make ist =
      { env_ist = push_let_rec_with IdMap.push (fun i cls -> compiled_closure cls cells.(i)) ist.env_ist el }
    in
    { d = (fun st n ist -> body.d st n (make ist)); s = None }
  | GTacCse (e, _, cse0, cse1) ->
    let e = compile_rt sc e in
    let cse0 = Array.map (compile_rt sc) cse0 in
    let cse1 = Array.map (fun (ids, b) -> (ids, compile_rt (scope_pushes sc (Array.to_list ids)) b)) cse1 in
    { d = (fun st n ist ->
        let v = match dsub e st n ist with
        | v -> v
        | exception Suspend s ->
          resume s (fun v st -> dcase st max_direct_depth ist v cse0 cse1)
        in
        dcase st n ist v cse0 cse1);
      s = None }
  | GTacCst (_, tag, (_ :: _ as el)) ->
    let el = List.map (compile_rt sc) el in
    let make vs = Valexpr.make_block tag (Array.of_list vs) in
    { d = (fun st n ist -> make (dargs_make st n ist make [] el)); s = None }
  | GTacOpn (kn, el) ->
    let el = List.map (compile_rt sc) el in
    let make vs = Tac2ffi.of_open (kn, Array.of_list vs) in
    { d = (fun st n ist -> make (dargs_make st n ist make [] el)); s = None }
  | GTacPrj (_, e, p) ->
    let e = compile_rt sc e in
    { d = (fun st n ist ->
        let v = match dsub e st n ist with
        | v -> v
        | exception Suspend s -> resume s (fun v _ -> Valexpr.field v p)
        in
        Valexpr.field v p);
      s = None }
  | GTacSet (_, e, p, r) ->
    let e = compile_rt sc e in
    let r = compile_rt sc r in
    let set v w = let () = Valexpr.set_field v p w in Valexpr.make_int 0 in
    let rest st n ist v =
      let w = match dsub r st n ist with
      | w -> w
      | exception Suspend s -> resume s (fun w _ -> set v w)
      in
      set v w
    in
    { d = (fun st n ist ->
        let v = match dsub e st n ist with
        | v -> v
        | exception Suspend s ->
          resume s (fun v st -> rest st max_direct_depth ist v)
        in
        rest st n ist v);
      s = None }
  | GTacFullMatch (e, brs) ->
    let e = compile_rt sc e in
    let brs = List.map (fun (pat, br) ->
        let bsc = match pattern_scope sc pat with Some bsc -> bsc | None -> [] in
        (pat, compile_rt bsc br)) brs
    in
    { d = (fun st n ist ->
        let v = match dsub e st n ist with
        | v -> v
        | exception Suspend s ->
          resume s (fun v st -> dfull_match st max_direct_depth ist v brs)
        in
        dfull_match st n ist v brs);
      s = None }
  | GTacWth { opn_match = e; opn_branch = cse; opn_default = (self, def) } ->
    let e = compile_rt sc e in
    let cse = KerName.Map.map (fun (self, ids, p) ->
        (self, ids, compile_rt (scope_pushes (scope_push sc self) (Array.to_list ids)) p)) cse
    in
    let def = compile_rt (scope_push sc self) def in
    { d = (fun st n ist ->
        let v = match dsub e st n ist with
        | v -> v
        | exception Suspend s ->
          resume s (fun v st -> dwith st max_direct_depth ist v cse self def)
        in
        dwith st n ist v cse self def);
      s = None }
  | GTacLet (true, _, _) | GTacCst (_, _, []) | GTacExt _
  | GTacAtm _ | GTacVar _ | GTacRef _ | GTacFun _ | GTacPrm _ ->
    { d = (fun _ _ ist -> tail (fun k -> bind_k (interp ist e) k)); s = None }

(** [enter c ist k]: the body of a compiled function, with code [c], run at run time on [ist] and
    [k] (its [run], [closure_value]): its direct code, with [k v] on a value [v], [s] on [Suspend
    s] with the continuation whose both parts are [k], and [t k] on [Tail t], is [bind_rt ist e k],
    [e] the body (Compiled bodies above). [s kk] and [t k] are OCaml tail calls, and [k] reaches
    a tail step unwrapped: a loop of tail calls through steps in the proof monad keeps no pending
    continuation, as in [bind_rt]. *)
and enter c ist k =
  match c.d NoState max_direct_depth ist with
  | v -> k v
  | exception Suspend s -> s { kv = k; ks = fun v _ -> k v }
  | exception Tail t -> t k

(** [dapply st n nargs f args]: [apply_bind_n nargs f args] in direct code. A pure primitive's
    value is the one [apply_bind_n] passes to [k]. A primitive that reads the environment and the
    evar map gives its value from [st], which holds them as [tclENV] and [tclEVARMAP] give them,
    and reading them has no effect; without [st] it suspends with [apply_bind_n]'s steps, and gives
    the value with the state it read. A primitive with a check gives the checked value, otherwise raises the
    tail step [apply_val f args >>= k]. A function given fewer arguments gives [apply_partial_val f
    args]. An Ltac2 function runs its direct run, whose result is that of [run args k]
    ([Tac2val.direct]). Anything else raises the tail step [apply_val f args >>= k], which is
    [apply_bind_n]'s. *)
and dapply st n nargs f args = match Tac2val.closure_direct f with
| Some (DirectPure (m, d)) when Int.equal m nargs -> d args
| Some (DirectEnv (m, d)) when Int.equal m nargs ->
  let g = d args in
  begin match st with
  | State (env, sigma) -> g env sigma
  | NoState ->
    suspend (fun kk -> Proofview.tclENV >>= fun env -> Proofview.tclEVARMAP >>= fun sigma ->
      kk.ks (g env sigma) (State (env, sigma)))
  end
| Some (DirectRun (m, _, d)) when Int.equal m nargs -> d st n args
| Some (DirectCheck (m, c)) when Int.equal m nargs ->
  begin match c args with
  | Some v -> v
  | None -> tail (fun k -> apply_val_bind f args k)
  end
| Some (DirectPure (m, _) | DirectEnv (m, _) | DirectRun (m, _, _) | DirectCheck (m, _)) when nargs < m ->
  Tac2val.apply_partial_val f args
| Some (DirectPure _ | DirectEnv _ | DirectRun _ | DirectCheck _) | None ->
  tail (fun k -> apply_val_bind f args k)

(** [dargs_app st n ist nargs f acc args]: the arguments [args] of a call of [f], after the values
    [acc] (newest first), from left to right, in direct code; on a suspension, the rest of them
    and the call, as direct code. *)
and dargs_app st n ist nargs f acc args = match args with
| [] -> List.rev acc
| c :: rest ->
  match dsub c st n ist with
  | v -> dargs_app st n ist nargs f (v :: acc) rest
  | exception Suspend s -> dargs_resume s ist nargs f acc rest

(** [dargs_resume s ist nargs f acc rest]: [dargs_app]'s suspension when the argument after [acc]
    suspends with [s], [rest] the arguments after it. *)
and dargs_resume : 'a. (cont -> valexpr Proofview.tactic) -> environment -> int -> valexpr ->
  valexpr list -> code list -> 'a = fun s ist nargs f acc rest ->
  resume s (fun v st ->
    dapply st max_direct_depth nargs f (dargs_app st max_direct_depth ist nargs f (v :: acc) rest))

(** {6 Calls of one to five arguments}

    [dapply1 st n f a] is [dapply st n 1 f [a]], and so on up to [dapply5]: where [f] carries the
    [Tac2val.fast] entry of that number of arguments ([Tac2val.closure_fast], under
    [closure_direct]'s test), [closure_direct f] gives the implementation of that same number of
    arguments, which [dapply] runs on the list of the arguments, and the entry is that
    implementation on the arguments one by one ([Tac2val.fast]): [Run] is [DirectRun]'s [drun],
    [Pure] is [DirectPure]'s function, [Check2] is [DirectCheck]'s, and [Env] is [DirectEnv]'s on
    the state when [st] holds it. Otherwise (no entry, another number of arguments, or [Env]
    without the state, where [dapply] suspends) it is [dapply] itself. So the steps are
    [dapply]'s, without the list of the arguments.

    [call_simple sc args st n ist f] and [call_args sc args st n ist f] are the call of [f] in
    [compile_node]: [dapply st n nargs f (args ist)] for simple [args], [dapply st n nargs f
    (dargs_app st n ist nargs f [] args)] otherwise. For up to five arguments they compute the
    arguments from left to right into variables, each not simple one with [dsub] and, on its
    suspension, [dargs_resume] with the values before it (newest first) and the arguments after
    it, as [dargs_app] does at that argument; then [dapply1] to [dapply5]. *)
and dapply1 st n f a = match Tac2val.closure_fast f with
| Run1 r -> r st n a
| Pure1 p -> p a
| Env1 g ->
  begin match st with
  | State (env, sigma) -> g a env sigma
  | NoState -> dapply st n 1 f [a]
  end
| _ -> dapply st n 1 f [a]

and dapply2 st n f a b = match Tac2val.closure_fast f with
| Run2 r -> r st n a b
| Pure2 p -> p a b
| Check2 c ->
  begin match c a b with
  | Some v -> v
  | None -> tail (fun k -> apply_val_bind f [a; b] k)
  end
| Env2 g ->
  begin match st with
  | State (env, sigma) -> g a b env sigma
  | NoState -> dapply st n 2 f [a; b]
  end
| _ -> dapply st n 2 f [a; b]

and dapply3 st n f a b c = match Tac2val.closure_fast f with
| Run3 r -> r st n a b c
| Pure3 p -> p a b c
| _ -> dapply st n 3 f [a; b; c]

and dapply4 st n f a b c d = match Tac2val.closure_fast f with
| Run4 r -> r st n a b c d
| _ -> dapply st n 4 f [a; b; c; d]

and dapply5 st n f a b c d e = match Tac2val.closure_fast f with
| Run5 r -> r st n a b c d e
| _ -> dapply st n 5 f [a; b; c; d; e]

and call_simple sc args = match List.map (compile_simple sc) args with
| [a1] -> fun st n ist f -> let x1 = a1 ist in dapply1 st n f x1
| [a1; a2] -> fun st n ist f -> let x1 = a1 ist in let x2 = a2 ist in dapply2 st n f x1 x2
| [a1; a2; a3] ->
  fun st n ist f -> let x1 = a1 ist in let x2 = a2 ist in let x3 = a3 ist in dapply3 st n f x1 x2 x3
| [a1; a2; a3; a4] ->
  fun st n ist f ->
    let x1 = a1 ist in let x2 = a2 ist in let x3 = a3 ist in let x4 = a4 ist in
    dapply4 st n f x1 x2 x3 x4
| [a1; a2; a3; a4; a5] ->
  fun st n ist f ->
    let x1 = a1 ist in let x2 = a2 ist in let x3 = a3 ist in let x4 = a4 ist in let x5 = a5 ist in
    dapply5 st n f x1 x2 x3 x4 x5
| _ ->
  let nargs = List.length args in
  let args = compile_simple_list sc args in
  fun st n ist f -> dapply st n nargs f (args ist)

and call_args sc args = match List.map (compile_rt sc) args with
| [c1] ->
  fun st n ist f ->
    let x1 = match dsub c1 st n ist with v -> v | exception Suspend s -> dargs_resume s ist 1 f [] [] in
    dapply1 st n f x1
| [c1; c2] ->
  fun st n ist f ->
    let x1 = match dsub c1 st n ist with v -> v | exception Suspend s -> dargs_resume s ist 2 f [] [c2] in
    let x2 = match dsub c2 st n ist with v -> v | exception Suspend s -> dargs_resume s ist 2 f [x1] [] in
    dapply2 st n f x1 x2
| [c1; c2; c3] ->
  fun st n ist f ->
    let x1 = match dsub c1 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 3 f [] [c2; c3] in
    let x2 = match dsub c2 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 3 f [x1] [c3] in
    let x3 = match dsub c3 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 3 f [x2; x1] [] in
    dapply3 st n f x1 x2 x3
| [c1; c2; c3; c4] ->
  fun st n ist f ->
    let x1 = match dsub c1 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 4 f [] [c2; c3; c4] in
    let x2 = match dsub c2 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 4 f [x1] [c3; c4] in
    let x3 = match dsub c3 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 4 f [x2; x1] [c4] in
    let x4 = match dsub c4 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 4 f [x3; x2; x1] [] in
    dapply4 st n f x1 x2 x3 x4
| [c1; c2; c3; c4; c5] ->
  fun st n ist f ->
    let x1 = match dsub c1 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 5 f [] [c2; c3; c4; c5] in
    let x2 = match dsub c2 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 5 f [x1] [c3; c4; c5] in
    let x3 = match dsub c3 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 5 f [x2; x1] [c4; c5] in
    let x4 = match dsub c4 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 5 f [x3; x2; x1] [c5] in
    let x5 = match dsub c5 st n ist with
    | v -> v | exception Suspend s -> dargs_resume s ist 5 f [x4; x3; x2; x1] [] in
    dapply5 st n f x1 x2 x3 x4 x5
| cs ->
  let nargs = List.length cs in
  fun st n ist f -> dapply st n nargs f (dargs_app st n ist nargs f [] cs)

(** [dargs_make st n ist make acc args]: [dargs_app] for the arguments of a constructor, which
    [make] builds. *)
and dargs_make st n ist make acc args = match args with
| [] -> List.rev acc
| c :: rest ->
  match dsub c st n ist with
  | v -> dargs_make st n ist make (v :: acc) rest
  | exception Suspend s ->
    resume s (fun v st ->
      make (dargs_make st max_direct_depth ist make (v :: acc) rest))

(** [dlet st n ist accu el body]: the bindings [el] of a let from [accu], their right-hand sides in
    [ist], in direct code, which gives the environment for the body; on a suspension, the rest of
    the bindings and the body, as direct code. *)
and dlet st n ist accu el body = match el with
| [] -> accu
| (na, c) :: rest ->
  match dsub c st n ist with
  | v -> dlet st n ist (cpush accu na v) rest body
  | exception Suspend s ->
    resume s (fun v st ->
      body.d st max_direct_depth (dlet st max_direct_depth ist (cpush accu na v) rest body))

(** [interp_case]/[case_rt], [interp_full_match] and [interp_with] in direct code: the same steps,
    with [cpush], then the branch's direct code in tail position. *)
and dcase st n ist v cse0 cse1 =
  if Valexpr.is_int v then
    cse0.(Tac2ffi.to_int v).d st n ist
  else
    let (tag, args) = Tac2ffi.to_block v in
    let (ids, c) = cse1.(tag) in
    c.d st n (cpush_array ist ids args)

and dfull_match st n ist v brs = match brs with
| [] -> CErrors.anomaly Pp.(str "ltac2 match not exhaustive")
| (pat, br) :: rest ->
  begin match cmatch_pattern ist pat v with
  | exception NoMatch -> dfull_match st n ist v rest
  | ist -> br.d st n ist
  end

and dwith st n ist v cse self def =
  let (kn, args) = Tac2ffi.to_open v in
  match KerName.Map.find_opt kn cse with
  | None -> def.d st n (cpush ist self v)
  | Some (self, ids, p) ->
    let ist = cpush ist self v in
    p.d st n (cpush_array ist ids args)

(** [compile_simple sc e], [e] simple: [compile_simple sc e ist] is [eval_simple ist e]. *)
and compile_simple sc e : scode = match e with
| GTacAtm (AtmInt n) -> fun _ -> Tac2ffi.of_int n
| GTacAtm (AtmStr s) -> fun _ -> Tac2ffi.of_string s
| GTacVar id ->
  begin match scope_find id sc with
  | Some (i, id) ->
    (* The [i]-th newest binding (from 0) if it binds this very object [id], otherwise [get_var ist
       id]. That is [get_var ist id]: a binding of [id] made with this object is the binding
       [IdMap.find] returns when no newer binding is of the same name, which the scope says
       (identifiers are hashconsed, so the test compares names, not binders). *)
    let rec walk j u ist = match u with
    | IdMap.Bind b ->
      if Int.equal j 0 then (if b.id == id then b.v else get_var ist id) else walk (j - 1) b.next ist
    | IdMap.Base _ -> get_var ist id
    in
    (* [walk i ist.env_ist ist], unrolled for the first three positions. *)
    begin match i with
    | 0 ->
      fun ist -> begin match ist.env_ist with
      | IdMap.Bind b when b.id == id -> b.v
      | IdMap.Bind _ | IdMap.Base _ -> get_var ist id
      end
    | 1 ->
      fun ist -> begin match ist.env_ist with
      | IdMap.Bind { next = IdMap.Bind b; _ } when b.id == id -> b.v
      | IdMap.Bind _ | IdMap.Base _ -> get_var ist id
      end
    | 2 ->
      fun ist -> begin match ist.env_ist with
      | IdMap.Bind { next = IdMap.Bind { next = IdMap.Bind b; _ }; _ } when b.id == id -> b.v
      | IdMap.Bind _ | IdMap.Base _ -> get_var ist id
      end
    | _ -> fun ist -> walk i ist.env_ist ist
    end
  | None -> fun ist -> get_var ist id
  end
| GTacRef kn ->
  let c = GlobalValue.cell () in
  fun _ -> GlobalValue.get_cell c compute_global kn
| GTacFun (ids, b) ->
  let cell = code_cell (scope_pushes sc ids) in
  fun ist -> compiled_closure { clos_ref = None; clos_env = ist.env_ist; clos_var = ids; clos_exp = b } cell
| GTacPrm ml -> fun _ -> Tac2env.interp_primitive ml
| GTacCst (_, n, []) -> fun _ -> Valexpr.make_int n
| GTacCst (_, n, el) ->
  let el = compile_simple_list sc el in
  fun ist -> Valexpr.make_block n (Array.of_list (el ist))
| GTacOpn (kn, el) ->
  let el = compile_simple_list sc el in
  fun ist -> Tac2ffi.of_open (kn, Array.of_list (el ist))
| GTacPrj (_, e, p) ->
  let e = compile_simple sc e in
  fun ist -> Valexpr.field (e ist) p
| GTacApp _ | GTacLet _ | GTacCse _ | GTacWth _ | GTacFullMatch _ | GTacSet _ | GTacExt _ ->
  anomaly (Pp.str "Term is not simple")

(** Left to right, as [eval_simple_list]. *)
and compile_simple_list sc = function
| [] -> fun _ -> []
| [a] ->
  let a = compile_simple sc a in
  fun ist -> [a ist]
| [a; b] ->
  let a = compile_simple sc a in
  let b = compile_simple sc b in
  fun ist -> let x = a ist in let y = b ist in [x; y]
| [a; b; c] ->
  let a = compile_simple sc a in
  let b = compile_simple sc b in
  let c = compile_simple sc c in
  fun ist -> let x = a ist in let y = b ist in let z = c ist in [x; y; z]
| e :: l ->
  let e = compile_simple sc e in
  let l = compile_simple_list sc l in
  fun ist -> let v = e ist in v :: l ist

let interp_value ist tac =
  eval_pure false ist.env_ist None tac

(** Cross-boundary hacks. *)

open Geninterp

let val_env : environment Val.typ = Val.create "ltac2:env"
let env_ref = Id.of_string_soft "@@ltac2_env@@"

let extract_env (Val.Dyn (tag, v)) : environment =
match Val.eq tag val_env with
| None -> assert false
| Some Refl -> v

let get_env ist =
  try extract_env (Id.Map.find env_ref ist)
  with Not_found -> empty_environment

let set_env env ist =
  Id.Map.add env_ref (Val.Dyn (val_env, env)) ist
