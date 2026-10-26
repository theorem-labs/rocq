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
  val get : (ltac_constant -> valexpr) -> ltac_constant -> valexpr
  (** [get compute kn] is [compute kn], computed once while the tables are the ones it was
      computed under. [compute] must read those tables only and have no other effect. *)
end =
struct

module KNTbl = Hashtbl.Make(struct
  type t = KerName.t
  let equal kn1 kn2 = kn1 == kn2 || KerName.equal kn1 kn2
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
    two words cost about 1 MB. *)
let bound = 65536

let table : entry KNTbl.t = KNTbl.create 512

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

let get compute kn =
  let globals = Tac2env.globals () in
  let compiled = Tac2env.compiled_globals () in
  let primitives = Tac2env.primitive_definitions () in
  let () =
    if globals != !table_globals || compiled != !table_compiled
       || not (Int.equal primitives !table_primitives)
    then begin
      KNTbl.reset table;
      table_globals := globals;
      table_compiled := compiled;
      table_primitives := primitives
    end
  in
  match KNTbl.find table kn with
  | Shared v -> v
  | Recompute -> compute kn
  | exception Not_found ->
    let v = compute kn in
    let () =
      if KNTbl.length table < bound then
        KNTbl.replace table kn (if shareable_global kn then Shared v else Recompute)
    in
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
  bind_ct ist e1 (fun v -> let_rt ist (push_name ist na v) el e)
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

and push_let_rec ist el =
  let map (na, e) = match e with
  | GTacFun (ids, e) ->
    let cls = { clos_ref = None; clos_env = ist; clos_var = ids; clos_exp = e } in
    let f = interp_closure cls in
    na, cls, f
  | _ -> anomaly (str "Ill-formed recursive function")
  in
  let fixs = List.map map el in
  let fold accu (na, _, cls) =match na with
    | Anonymous -> accu
    | Name id -> IdMap.add id cls accu
  in
  let ist = List.fold_left fold ist fixs in
  (* Hack to make a cycle imperatively in the environment *)
  let iter (_, e, _) = e.clos_env <- ist in
  let () = List.iter iter fixs in
  ist

and interp_closure f =
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
  Tac2ffi.(of_closure (abstract (List.length f.clos_var) ans))

(** [interp_case] runs at run time only: in the continuation of the scrutinee's value. *)
and interp_case ist e cse0 cse1 =
  if Valexpr.is_int e then
    interp_rt ist cse0.(Tac2ffi.to_int e)
  else
    let (n, args) = Tac2ffi.to_block e in
    let (ids, e) = cse1.(n) in
    let ist = CArray.fold_left2 push_name ist ids args in
    interp_rt ist e

(** {6 Run time}

    [interp ist e] builds a tactic: the arms above compute some values when they are called (a
    variable, a global, a closure) and bind the rest. Where [interp] is called matters: the body of a
    closure is built when the closure is applied, and [Proofview.Goal.enter] (Control.enter) applies
    a closure under a handler that turns an exception raised while building the tactic into a
    failure of the tactic, while an exception raised while it runs goes through. So a primitive,
    which can raise, must not run where stock only builds.

    The functions below ([*_rt], [bind_rt], [apply_bind], [apply_tail], [args_rt], [let_rt],
    [interp_case]) are called only at run time: in the continuation of a bind, or from another
    of them. There, building a tactic and running it are one step: a continuation's tactic is
    built and run at once, every time the continuation runs. So the values that stock computes in
    a chain of [return v >>= k] are computed here directly, in the same order, and passed to the
    OCaml continuation [k]. [return v >>= k] runs [k v] once, with no effect in between, each
    time it runs; [Logic_monad.Logical]'s [return] and [bind] install no exception handler, so a
    computation that raises raises through the same handlers in both. So the values, the effects
    and their order, the run counts under backtracking, the exceptions and the proof state are
    stock's. The binds left out are those of [return] only: every primitive with an effect, every
    Ltac2 closure and every other construct still goes through the proof monad as in stock.

    A pure primitive ([Tac2val.closure_direct]) applied to exactly as many arguments as it takes
    is, in stock, [tclUNIT () >>= fun () -> tclUNIT (f args)] (or reads the environment and the
    evar map first, [DirectEnv]); at run time [f args] is computed directly.

    OCaml stack: chains of lets, arguments and branches are tail calls; the fallback of [bind_rt]
    ([interp_rt ist e >>= k]) is not, so a nest of non-simple arguments, scrutinees or right-hand
    sides uses stack in proportion to its depth, as internalization of the same expression does. *)

(** [bind_ct ist e k]: the tactic [interp ist e >>= k], built at construction time. [k] runs only
    in a continuation. *)
and bind_ct ist e k = match e with
| GTacApp (f, args) when simple_args args ->
  (* [interp ist (GTacApp (f, args))] binds [interp ist f] to [apply_val f (eval_simple_list ist
     args)]; [>>= k] associates into its continuation. *)
  interp ist f >>= fun f -> apply_bind f (eval_simple_list ist args) k
| _ -> interp ist e >>= k

(** [bind_rt ist e k], at run time: [interp ist e >>= k]. *)
and bind_rt ist e k =
  if simple_fuel max_simple_nodes e >= 0 then k (eval_simple ist e)
  else match e with
  | GTacApp (f, args) when simple_fuel max_simple_nodes f >= 0 && simple_args args ->
    let f = eval_simple ist f in
    apply_bind f (eval_simple_list ist args) k
  | _ -> interp_rt ist e >>= k

(** [apply_bind f args k], at run time: [Tac2val.apply_val f args >>= k]. *)
and apply_bind f args k = match Tac2val.closure_direct f with
| Some (DirectPure (n, d)) when Int.equal n (List.length args) -> k (d args)
| Some (DirectEnv (n, d)) when Int.equal n (List.length args) ->
  let d = d args in
  Proofview.tclENV >>= fun env -> Proofview.tclEVARMAP >>= fun sigma -> k (d env sigma)
| Some (DirectPure _ | DirectEnv _) | None -> Tac2val.apply_val f args >>= k

(** [apply_tail f args], at run time: [Tac2val.apply_val f args]. *)
and apply_tail f args = match Tac2val.closure_direct f with
| Some (DirectPure (n, d)) when Int.equal n (List.length args) -> return (d args)
| Some (DirectEnv (n, d)) when Int.equal n (List.length args) ->
  let d = d args in
  Proofview.tclENV >>= fun env -> Proofview.tclEVARMAP >>= fun sigma -> return (d env sigma)
| Some (DirectPure _ | DirectEnv _) | None -> Tac2val.apply_val f args

(** [args_rt ist acc args k], at run time: [Proofview.Monad.List.map (interp ist) args >>= fun l ->
    k (List.rev_append acc l)], the arguments from left to right. *)
and args_rt ist acc args k = match args with
| [] -> k (List.rev acc)
| e :: args -> bind_rt ist e (fun v -> args_rt ist (v :: acc) args k)

(** [let_rt ist accu el e], at run time: the rest of a [GTacLet (false, _, e)] from the accumulated
    environment [accu]: the fold of [GTacLet]'s arm over [el], then [e]. The right-hand sides are
    evaluated in [ist]. *)
and let_rt ist accu el e = match el with
| [] -> interp_rt accu e
| (na, e') :: el -> bind_rt ist e' (fun v -> let_rt ist (push_name accu na v) el e)

(** [interp_rt ist e], at run time: [interp ist e]. *)
and interp_rt ist e =
  if simple_fuel max_simple_nodes e >= 0 then return (eval_simple ist e)
  else match e with
  | GTacApp (f, args) when simple_fuel max_simple_nodes f >= 0 ->
    let f = eval_simple ist f in
    if simple_args args then apply_tail f (eval_simple_list ist args)
    else args_rt ist [] args (fun args -> apply_tail f args)
  | GTacLet (false, el, e) -> let_rt ist ist el e
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

and compute_global kn =
  match Tac2env.get_compiled_global kn with
  | Some (_info,v) -> v
  | None -> match Tac2env.interp_global kn with
    | exception Not_found -> anomaly (str "Unbound reference" ++ KerName.print kn)
    | { gdata_expr = e } -> eval_pure IdMap.empty (Some kn) e

and eval_pure bnd kn = function
| GTacVar id -> IdMap.get id bnd
| GTacAtm (AtmInt n) -> Valexpr.make_int n
| GTacRef kn -> eval_global kn
| GTacFun (na, e) ->
  let cls = { clos_ref = kn; clos_env = bnd; clos_var = na; clos_exp = e } in
  interp_closure cls
| GTacCst (_, n, []) -> Valexpr.make_int n
| GTacCst (_, n, el) -> Valexpr.make_block n (eval_pure_args bnd el)
| GTacOpn (kn, el) -> Tac2ffi.of_open (kn, eval_pure_args bnd el)
| GTacLet (false, vals, body) ->
  let fold accu (na, e) = match na with
  | Anonymous ->
    (* No need to evaluate, we know this is a value *)
    accu
  | Name id ->
    let v = eval_pure bnd None e in
    IdMap.add id v accu
  in
  let bnd = List.fold_left fold bnd vals in
  eval_pure bnd kn body
| GTacLet (true, el, body) ->
  let bnd = push_let_rec bnd el in
  eval_pure bnd kn body
| GTacPrj (_,e,i) ->
  let v = eval_pure bnd kn e in
  Valexpr.field v i

| GTacPrm ml -> Tac2env.interp_primitive ml

| GTacAtm (AtmStr _) | GTacSet _
| GTacApp _ | GTacCse _
| GTacExt _ | GTacWth _
| GTacFullMatch _ ->
  anomaly (Pp.str "Term is not a syntactical value")

and eval_pure_args bnd args =
  let map e = eval_pure bnd None e in
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

let interp_value ist tac =
  eval_pure ist.env_ist None tac

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
