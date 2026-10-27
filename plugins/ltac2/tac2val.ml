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
open Proofview.Notations

type ('a, _) arity0 =
| OneAty : ('a, 'a -> 'a Proofview.tactic) arity0
| AddAty : ('a, 'b) arity0 -> ('a, 'a -> 'b) arity0

type tag = int

type valexpr =
| ValInt of int
  (** Immediate integers *)
| ValBlk of tag * valexpr array
  (** Structured blocks *)
| ValStr of Bytes.t
  (** Strings *)
| ValCls of closure
  (** Closures *)
| ValOpn of KerName.t * valexpr array
  (** Open constructors *)
| ValExt : 'a Tac2dyn.Val.tag * 'a -> valexpr
  (** Arbitrary data *)

and closure =
| MLTactic : (valexpr, 'v) arity0 * Tac2expr.frame option * 'v * direct option * fast -> closure

(** The direct implementation of a pure primitive or of an Ltac2 closure: see the interface. *)
and direct =
| DirectPure of int * (valexpr list -> valexpr)
| DirectEnv of int * (valexpr list -> Environ.env -> Evd.evar_map -> valexpr)
| DirectRun of int * (valexpr list -> (valexpr -> valexpr Proofview.tactic) -> valexpr Proofview.tactic)
    * (state -> int -> valexpr list -> valexpr)
| DirectCheck of int * (valexpr list -> valexpr option)

(** The direct implementation for one number of arguments, without the list: see the interface. *)
and fast =
| NoFast
| Pure1 of (valexpr -> valexpr)
| Pure2 of (valexpr -> valexpr -> valexpr)
| Pure3 of (valexpr -> valexpr -> valexpr -> valexpr)
| Env1 of (valexpr -> Environ.env -> Evd.evar_map -> valexpr)
| Env2 of (valexpr -> valexpr -> Environ.env -> Evd.evar_map -> valexpr)
| Check2 of (valexpr -> valexpr -> valexpr option)
| Run1 of (state -> int -> valexpr -> valexpr)
| Run2 of (state -> int -> valexpr -> valexpr -> valexpr)
| Run3 of (state -> int -> valexpr -> valexpr -> valexpr -> valexpr)
| Run4 of (state -> int -> valexpr -> valexpr -> valexpr -> valexpr -> valexpr)
| Run5 of (state -> int -> valexpr -> valexpr -> valexpr -> valexpr -> valexpr -> valexpr)

and state =
| NoState
| State of Environ.env * Evd.evar_map

type cont = {
  kv : valexpr -> valexpr Proofview.tactic;
  ks : valexpr -> state -> valexpr Proofview.tactic;
}

exception Suspend of (cont -> valexpr Proofview.tactic)

exception Tail of ((valexpr -> valexpr Proofview.tactic) -> valexpr Proofview.tactic)

let arity_one = OneAty
let arity_suc a = AddAty a

type 'a arity = (valexpr, 'a) arity0

let mk_closure arity f = MLTactic (arity, None, f, None, NoFast)

let mk_closure_direct ?(fast = NoFast) arity f d = MLTactic (arity, None, f, Some d, fast)

let mk_closure_val arity f = ValCls (mk_closure arity f)

module Valexpr =
struct

type t = valexpr

let is_int = function
| ValInt _ -> true
| ValBlk _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ -> false

let tag v = match v with
| ValBlk (n, _) -> n
| ValInt _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ ->
  CErrors.anomaly (Pp.str "Unexpected value shape")

let field v n = match v with
| ValBlk (_, v) -> v.(n)
| ValInt _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ ->
  CErrors.anomaly (Pp.str "Unexpected value shape")

let set_field v n w = match v with
| ValBlk (_, v) -> v.(n) <- w
| ValInt _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ ->
  CErrors.anomaly (Pp.str "Unexpected value shape")

let make_block tag v = ValBlk (tag, v)
let make_int n = ValInt n

end

let to_closure = function
| ValCls cls -> cls
| ValExt _ | ValInt _ | ValBlk _ | ValStr _ | ValOpn _ -> assert false

let wrap fr tac = match fr with
  | None -> tac
  | Some fr -> Tac2bt.with_frame fr tac

(* [wrap fr tac] is [tac] itself exactly when this is true when [wrap] runs: [Tac2bt.with_frame]
   reads its two flags when it is called. *)
let[@inline] wrap_is_identity fr = match fr with
  | None -> true
  | Some _ -> Tac2bt.with_frame_is_identity ()

let[@inline] closure_direct v = match v with
  | ValCls (MLTactic (_, fr, _, (Some _ as d), _)) -> if wrap_is_identity fr then d else None
  | ValCls (MLTactic (_, _, _, None, _)) | ValInt _ | ValBlk _ | ValStr _ | ValOpn _ | ValExt _ -> None

(* [closure_direct]'s test, for the [fast] entry: a closure carries [NoFast] when it carries no
   direct implementation. *)
let[@inline] closure_fast v = match v with
  | ValCls (MLTactic (_, fr, _, _, fast)) -> if wrap_is_identity fr then fast else NoFast
  | ValInt _ | ValBlk _ | ValStr _ | ValOpn _ | ValExt _ -> NoFast

(** [partial_direct d given]: the direct implementation of the closure that [apply] returns when
    a closure carrying [d] gets the arguments [given] (newest first), fewer than it takes. That
    closure, applied to the [n - m] remaining arguments [rest], is [apply] of the first closure
    to [given @ rest]: [apply] passes each argument to the curried function, so both end in [wrap
    fr (f a1 ... an)] with the same frame [fr]. So [d], given [given @ rest], is its direct
    implementation, as [direct] describes; [closure_direct] checks the same frame on it. *)
let partial_direct d rgiven = match d with
  | None -> None
  | Some d ->
    let given = List.rev rgiven in
    let m = List.length given in
    Some (match d with
    | DirectPure (n, f) -> DirectPure (n - m, fun rest -> f (given @ rest))
    | DirectEnv (n, f) -> DirectEnv (n - m, fun rest -> f (given @ rest))
    | DirectRun (n, f, df) ->
      DirectRun (n - m, (fun rest k -> f (given @ rest) k), (fun st fuel rest -> df st fuel (given @ rest)))
    | DirectCheck (n, f) -> DirectCheck (n - m, fun rest -> f (given @ rest)))

(** [partial_fast fast given]: the [fast] entry of the closure that [apply] returns when a closure
    carrying [fast] gets the arguments [given] (newest first), fewer than it takes. As in
    [partial_direct], that closure applied to [rest] is the first one applied to [given @ rest],
    whose [fast] entry is the first one's applied to the arguments of [given] (oldest first) and
    then to [rest]. Given no argument, it is the first one's entry itself. A [Check2] entry has
    no entry of one argument. *)
let partial_fast fast rgiven = match fast, rgiven with
  | _, [] -> fast
  | Pure2 f, [a] -> Pure1 (fun b -> f a b)
  | Pure3 f, [a] -> Pure2 (fun b c -> f a b c)
  | Pure3 f, [b; a] -> Pure1 (fun c -> f a b c)
  | Env2 f, [a] -> Env1 (fun b env sigma -> f a b env sigma)
  | Run2 f, [a] -> Run1 (fun st n b -> f st n a b)
  | Run3 f, [a] -> Run2 (fun st n b c -> f st n a b c)
  | Run3 f, [b; a] -> Run1 (fun st n c -> f st n a b c)
  | Run4 f, [a] -> Run3 (fun st n b c d -> f st n a b c d)
  | Run4 f, [b; a] -> Run2 (fun st n c d -> f st n a b c d)
  | Run4 f, [c; b; a] -> Run1 (fun st n d -> f st n a b c d)
  | Run5 f, [a] -> Run4 (fun st n b c d e -> f st n a b c d e)
  | Run5 f, [b; a] -> Run3 (fun st n c d e -> f st n a b c d e)
  | Run5 f, [c; b; a] -> Run2 (fun st n d e -> f st n a b c d e)
  | Run5 f, [d; c; b; a] -> Run1 (fun st n e -> f st n a b c d e)
  | (NoFast | Pure1 _ | Pure2 _ | Pure3 _ | Env1 _ | Env2 _ | Check2 _
    | Run1 _ | Run2 _ | Run3 _ | Run4 _ | Run5 _), _ -> NoFast

let partial_value arity fr f d fast given =
  ValCls (MLTactic (arity, fr, f, partial_direct d given, partial_fast fast given))

let rec apply : type a. a arity -> _ -> a -> direct option -> fast -> valexpr list -> valexpr list -> valexpr Proofview.tactic =
  fun arity fr f d fast given args -> match args, arity with
  | [], arity -> Proofview.tclUNIT (partial_value arity fr f d fast given)
  (* A few hardcoded cases for efficiency *)
  | [a0], OneAty -> wrap fr (f a0)
  | [a0; a1], AddAty OneAty -> wrap fr (f a0 a1)
  | [a0; a1; a2], AddAty (AddAty OneAty) -> wrap fr (f a0 a1 a2)
  | [a0; a1; a2; a3], AddAty (AddAty (AddAty OneAty)) -> wrap fr (f a0 a1 a2 a3)
  (* Generic cases *)
  | a :: args, OneAty ->
    wrap fr (f a) >>= fun f ->
    let MLTactic (arity, fr, f, d, fast) = to_closure f in
    apply arity fr f d fast [] args
  | a :: args, AddAty arity ->
    apply arity fr (f a) d fast (a :: given) args

let apply (MLTactic (arity, wrap, f, d, fast)) args = apply arity wrap f d fast [] args

let apply_val v args = apply (to_closure v) args

(* Fewer arguments than the closure takes reach [apply]'s first arm through its last one, once per
   argument (the hardcoded arms take exactly as many arguments as the arity): [apply_partial] does
   those steps and gives the value that [apply] returns in [tclUNIT]. *)
let rec apply_partial : type a. a arity -> _ -> a -> direct option -> fast -> valexpr list -> valexpr list -> valexpr =
  fun arity fr f d fast given args -> match args, arity with
  | [], arity -> partial_value arity fr f d fast given
  | a :: args, AddAty arity -> apply_partial arity fr (f a) d fast (a :: given) args
  | _ :: _, OneAty -> invalid_arg "Tac2val.apply_partial"

let apply_partial_val v args =
  let MLTactic (arity, fr, f, d, fast) = to_closure v in
  apply_partial arity fr f d fast [] args

type n_closure =
| NClosure : 'a arity * (valexpr list -> 'a) -> n_closure

let rec abstract n f =
  if Int.equal n 1 then NClosure (OneAty, fun accu v -> f (List.rev (v :: accu)))
  else
    let NClosure (arity, fe) = abstract (n - 1) f in
    NClosure (AddAty arity, fun accu v -> fe (v :: accu))

let abstract n f =
  match n with
  | 1 -> MLTactic (OneAty, None, (fun a -> f [a]), None, NoFast)
  | 2 -> MLTactic (AddAty OneAty, None, (fun a b -> f [a;b]), None, NoFast)
  | 3 -> MLTactic (AddAty (AddAty OneAty), None, (fun a b c -> f [a;b;c]), None, NoFast)
  | 4 -> MLTactic (AddAty (AddAty (AddAty OneAty)), None, (fun a b c d -> f [a;b;c;d]), None, NoFast)
  | _ ->
    let () = assert (n > 0) in
    let NClosure (arity, f) = abstract n f in
    MLTactic (arity, None, f [], None, NoFast)

let abstract_run ?(fast = NoFast) n f run drun =
  let MLTactic (arity, fr, f, _, _) = abstract n f in
  MLTactic (arity, fr, f, Some (DirectRun (n, run, drun)), fast)

let annotate_closure fr (MLTactic (arity, fr0, f, d, fast)) =
  assert (Option.is_empty fr0);
  MLTactic (arity, Some fr, f, d, fast)

let rec purify_closure : type a. a arity -> (unit -> a) -> a = fun arity f ->
  match arity with
  | OneAty -> (fun x -> Proofview.tclUNIT () >>= fun () -> f () x)
  | AddAty a -> (fun x -> purify_closure a (fun () -> f () x))

let purify_closure ar f = purify_closure ar (fun () -> f)
