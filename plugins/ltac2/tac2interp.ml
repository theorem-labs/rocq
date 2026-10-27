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
      kept is worth compiling: [compiled_closure]). *)

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

let get compute kn =
  let () = check_tables () in
  fst (get_entry compute kn)

(** A cell keeps the value of a [Shared] entry and the [epoch] it was read in. While [epoch] has
    not changed, the tables are the ones the entry was computed under and the entry is still
    there, unchanged, so [get] would return that same value. *)
type cell = { mutable c_epoch : int; mutable c_value : valexpr }

let cell () = { c_epoch = -1; c_value = ValInt 0 }

let get_cell c compute kn =
  let () = check_tables () in
  if Int.equal c.c_epoch !epoch then c.c_value
  else
    let v, shared = get_entry compute kn in
    let () = if shared then begin c.c_epoch <- !epoch; c.c_value <- v end in
    v

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

(** Compiled code (see "Compiled bodies" below): [rcode] runs an expression at run time with a
    continuation, [scode] computes the value of a simple expression. *)
type rcode = environment -> (valexpr -> valexpr Proofview.tactic) -> valexpr Proofview.tactic
type scode = environment -> valexpr

(** A compile-time scope: the identifiers that the newest bindings of the environment bind, newest
    first, each the very object that its binder binds; older bindings are not known. Compiled code
    reads a variable of the scope at its position ([IdMap.find_at]), any other one by name. *)
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

(** [(List.fold_left2 cpush { env_ist = env } ids args).env_ist]. *)
let rec push_args env ids args = match ids, args with
| [], [] -> env
| Anonymous :: ids, _ :: args -> push_args env ids args
| Name id :: ids, v :: args -> push_args (IdMap.push id v env) ids args
| _ -> invalid_arg "List.fold_left2"

(** [get_var ist id], [id] the binder object at position [i] of the scope ([IdMap.find_at] is
    [IdMap.find]). *)
let get_var_at i id ist =
  try IdMap.find_at i id ist.env_ist with Not_found ->
    anomaly (str "Unbound variable " ++ Id.print id)

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
type code_cell = { mutable code : rcode option; scope : scope }

let code_cell scope = { code = None; scope }

(** At most this many nested calls of [compile_rt] in one compilation (see [compile_rt]). *)
let max_compile_depth = 256

let compile_depth = ref 0

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

and interp_closure f =
  closure_value (fun env ids args -> List.fold_left2 push_name { env_ist = env } ids args) f
    (fun ist k -> bind_rt ist f.clos_exp k)

(** The function of [f] whose body, when it runs directly, is [f]'s compiled body, kept in
    [cell] (see "Compiled bodies" below); its arguments are then bound with [IdMap.push], in the
    order of [cell.scope]. *)
and compiled_closure f cell =
  closure_value (fun env ids args -> { env_ist = push_args env ids args }) f
    (fun ist k -> body_code cell f.clos_exp ist k)

(** [closure_value bind f body]: the value of the function [f], whose body runs at run time as
    [body ist k] ([bind_rt ist f.clos_exp k], or the same compiled), its arguments bound by [bind]
    ([push_name] or [IdMap.push] over the arguments, whose environments give the same lookups). *)
and closure_value bind f body =
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
  Tac2ffi.of_closure (Tac2val.abstract_run (List.length f.clos_var) ans run)

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
  | _ -> interp_rt ist e >>= k

(** [apply_bind f args k], at run time: [Tac2val.apply_val f args >>= k]. *)
and apply_bind f args k = apply_bind_n (List.length args) f args k

(** [apply_bind_n n f args k] is [apply_bind f args k] for [args] of length [n]. *)
and apply_bind_n nargs f args k = match Tac2val.closure_direct f with
| Some (DirectPure (n, d)) when Int.equal n nargs -> k (d args)
| Some (DirectEnv (n, d)) when Int.equal n nargs ->
  let d = d args in
  Proofview.tclENV >>= fun env -> Proofview.tclEVARMAP >>= fun sigma -> k (d env sigma)
| Some (DirectRun (n, d)) when Int.equal n nargs -> d args k
| Some (DirectPure _ | DirectEnv _ | DirectRun _) | None -> Tac2val.apply_val f args >>= k

(** [apply_tail f args], at run time: [Tac2val.apply_val f args], which is
    [Tac2val.apply_val f args >>= return]. *)
and apply_tail f args = match Tac2val.closure_direct f with
| Some (DirectPure (n, d)) when Int.equal n (List.length args) -> return (d args)
| Some (DirectEnv (n, d)) when Int.equal n (List.length args) ->
  let d = d args in
  Proofview.tclENV >>= fun env -> Proofview.tclEVARMAP >>= fun sigma -> return (d env sigma)
| Some (DirectRun (n, d)) when Int.equal n (List.length args) -> d args return
| Some (DirectPure _ | DirectEnv _ | DirectRun _) | None -> Tac2val.apply_val f args

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
  | Some (_info,v) -> v
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

    [compile_rt e] is [bind_rt _ e] with every decision that depends on [e] alone taken once, when
    [e] is compiled: [compile_rt e ist k] runs what [bind_rt ist e k] runs, which at run time is
    [interp ist e >>= k] (Run time above). Those decisions are the ones [bind_rt], [interp_rt],
    [eval_simple], [args_rt], [let_rt] and [case_rt] take by looking at the expression: whether it
    is simple ([simple_fuel], a function of [e]) and which node it is. What depends on values (the
    function applied, its direct implementation and arity, the branch taken, the value of a
    global) is still decided when the code runs, by the same functions ([apply_bind],
    [GlobalValue]). Compiling reads [e] and allocates; it has no other effect, so when it happens
    cannot be observed. Compiled code runs only where [bind_rt] may run: in [closure_value]'s
    [run], at run time.

    The compiled code also runs at once the constructs that [bind_rt] gives to [interp] (its
    fallback, [interp_rt ist e >>= k]): an application whose head is not simple, a constructor,
    open constructor or projection that is not simple, a write to a field, a full match, a match
    on an open type and a recursive let. For each, the code below is [interp]'s arm run with [>>=
    k] at run time: [interp ist e' >>= f] of each subexpression [e'] is [compile_rt e' ist f] (by
    induction on the expression), [Proofview.Monad.List.map] of [interp] over subexpressions is
    [args_c] (as [args_rt] is), [return v >>= k] is [k v], and [(m >>= f) >>= k] is [m >>= fun v ->
    f v >>= k] (Run time above: no handler is moved, nothing runs in between). The pure steps of
    the arm (building the value, matching the patterns, writing the field, making the recursive
    functions, binding the variables) happen in the same continuation and in the same order as
    in [interp]. Extension nodes ([GTacExt]) still go through [interp].

    Functions made by compiled code (a [GTacFun], a recursive let) are [compiled_closure]s with one
    [code_cell] per [GTacFun] node: every function made from that node runs the one compiled body,
    compiled when one of them first runs; each has its own environment, read when it is applied,
    as in [closure_value]. A global read by compiled code goes through one [GlobalValue.cell] per
    [GTacRef] node ([GlobalValue.get_cell] is [GlobalValue.get]). As in [eval_simple], strings,
    integers and constructors are made anew at each evaluation. *)

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
    above). So a subexpression deeper than [max_compile_depth] nested compiles is not compiled:
    its code is [bind_rt ist e k], which is what compiled code runs ([compile_rt e ist k] is
    [bind_rt ist e k]). [bind_rt] reads variables by name and binds with [IdMap.add], whose lookups
    give what [IdMap.push]'s give, so the environment compiled code made serves it as is, and
    what it binds stays in its own continuations: the compiled code after it reads the
    environment it closed over. Compiling never runs code, so [compile_depth] counts the nested
    calls of one compilation only; it is back to 0 when [compile_rt] returns or raises. *)
and compile_rt sc e : rcode =
  if !compile_depth >= max_compile_depth then (fun ist k -> bind_rt ist e k)
  else begin
    incr compile_depth;
    match compile_node sc e with
    | c -> decr compile_depth; c
    | exception ex -> let ex = Exninfo.capture ex in decr compile_depth; Exninfo.iraise ex
  end

and compile_node sc e : rcode =
  if simple_fuel max_simple_nodes e >= 0 then
    let s = compile_simple sc e in
    fun ist k -> k (s ist)
  else match e with
  | GTacApp (f, args) ->
    let nargs = List.length args in
    let call =
      if simple_args args then
        let args = compile_simple_list sc args in
        fun ist f k -> apply_bind_n nargs f (args ist) k
      else
        let args = List.map (compile_rt sc) args in
        fun ist f k -> args_c ist [] args (fun args -> apply_bind_n nargs f args k)
    in
    if simple_fuel max_simple_nodes f >= 0 then
      let f = compile_simple sc f in
      fun ist k -> let f = f ist in call ist f k
    else
      (* [interp]'s arm: [interp ist f >>= fun f -> X], [X] the same call. *)
      let f = compile_rt sc f in
      fun ist k -> f ist (fun f -> call ist f k)
  | GTacLet (false, el, body) ->
    let el' = List.map (fun (na, e) -> (na, compile_rt sc e)) el in
    let body = compile_rt (scope_pushes sc (List.map fst el)) body in
    fun ist k -> let_c ist ist el' (fun accu -> body accu k)
  | GTacLet (true, el, body)
    when List.for_all (fun (_, e) -> match e with GTacFun _ -> true | _ -> false) el ->
    let sc = scope_pushes sc (List.map fst el) in
    let cells = Array.of_list (List.map (fun (_, e) -> match e with
      | GTacFun (ids, _) -> code_cell (scope_pushes sc ids)
      | _ -> assert false) el)
    in
    let body = compile_rt sc body in
    fun ist k ->
      let ist = push_let_rec_with IdMap.push (fun i cls -> compiled_closure cls cells.(i)) ist.env_ist el in
      body { env_ist = ist } k
  | GTacCse (e, _, cse0, cse1) ->
    let e = compile_rt sc e in
    let cse0 = Array.map (compile_rt sc) cse0 in
    let cse1 = Array.map (fun (ids, b) -> (ids, compile_rt (scope_pushes sc (Array.to_list ids)) b)) cse1 in
    fun ist k -> e ist (fun v -> case_c ist v cse0 cse1 k)
  | GTacCst (_, n, (_ :: _ as el)) ->
    let el = List.map (compile_rt sc) el in
    fun ist k -> args_c ist [] el (fun vs -> k (Valexpr.make_block n (Array.of_list vs)))
  | GTacOpn (kn, el) ->
    let el = List.map (compile_rt sc) el in
    fun ist k -> args_c ist [] el (fun vs -> k (Tac2ffi.of_open (kn, Array.of_list vs)))
  | GTacPrj (_, e, p) ->
    let e = compile_rt sc e in
    fun ist k -> e ist (fun v -> k (Valexpr.field v p))
  | GTacSet (_, e, p, r) ->
    let e = compile_rt sc e in
    let r = compile_rt sc r in
    fun ist k -> e ist (fun v -> r ist (fun w -> let () = Valexpr.set_field v p w in k (Valexpr.make_int 0)))
  | GTacFullMatch (e, brs) ->
    let e = compile_rt sc e in
    let brs = List.map (fun (pat, br) ->
        let bsc = match pattern_scope sc pat with Some bsc -> bsc | None -> [] in
        (pat, compile_rt bsc br)) brs
    in
    fun ist k -> e ist (fun v -> full_match_c ist v brs k)
  | GTacWth { opn_match = e; opn_branch = cse; opn_default = (self, def) } ->
    let e = compile_rt sc e in
    let cse = KerName.Map.map (fun (self, ids, p) ->
        (self, ids, compile_rt (scope_pushes (scope_push sc self) (Array.to_list ids)) p)) cse
    in
    let def = compile_rt (scope_push sc self) def in
    fun ist k -> e ist (fun v -> with_c ist v cse self def k)
  | GTacLet (true, _, _) | GTacCst (_, _, []) | GTacExt _
  | GTacAtm _ | GTacVar _ | GTacRef _ | GTacFun _ | GTacPrm _ ->
    fun ist k -> interp ist e >>= k

(** [args_c ist acc args k]: [args_rt] on compiled arguments. *)
and args_c ist acc args k = match args with
| [] -> k (List.rev acc)
| c :: args -> c ist (fun v -> args_c ist (v :: acc) args k)

(** [let_c ist accu el fin]: [let_rt] on compiled right-hand sides. *)
and let_c ist accu el fin = match el with
| [] -> fin accu
| (na, c) :: el -> c ist (fun v -> let_c ist (cpush accu na v) el fin)

(** [case_c ist v cse0 cse1 k]: [case_rt ist v _ _ (fun ist br -> bind_rt ist br k)] on compiled
    branches. *)
and case_c ist v cse0 cse1 k =
  if Valexpr.is_int v then
    cse0.(Tac2ffi.to_int v) ist k
  else
    let (n, args) = Tac2ffi.to_block v in
    let (ids, c) = cse1.(n) in
    c (CArray.fold_left2 cpush ist ids args) k

(** [full_match_c ist v brs k]: [interp_full_match ist v brs >>= k] on compiled branches. *)
and full_match_c ist v brs k = match brs with
| [] -> CErrors.anomaly Pp.(str "ltac2 match not exhaustive")
| (pat, br) :: rest ->
  begin match cmatch_pattern ist pat v with
  | exception NoMatch -> full_match_c ist v rest k
  | ist -> br ist k
  end

(** [with_c ist v cse self def k]: [interp_with ist v cse (self, def) >>= k] on compiled branches. *)
and with_c ist v cse self def k =
  let (kn, args) = Tac2ffi.to_open v in
  match KerName.Map.find_opt kn cse with
  | None -> def (cpush ist self v) k
  | Some (self, ids, p) ->
    let ist = cpush ist self v in
    let ist = CArray.fold_left2 cpush ist ids args in
    p ist k

(** [compile_simple sc e], [e] simple: [compile_simple sc e ist] is [eval_simple ist e]. *)
and compile_simple sc e : scode = match e with
| GTacAtm (AtmInt n) -> fun _ -> Tac2ffi.of_int n
| GTacAtm (AtmStr s) -> fun _ -> Tac2ffi.of_string s
| GTacVar id ->
  begin match scope_find id sc with
  | Some (i, id) -> fun ist -> get_var_at i id ist
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
