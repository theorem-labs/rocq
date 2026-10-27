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

(** {5 Toplevel values} *)

(** {5 Dynamic semantics} *)

(** Values are represented in a way similar to OCaml, i.e. they contrast
    immediate integers (integers, constructors without arguments) and structured
    blocks (tuples, arrays, constructors with arguments), as well as a few other
    base cases, namely closures, strings, named constructors, and dynamic type
    coming from the Rocq implementation. *)

type tag = int

type closure

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

module Valexpr :
sig
  type t = valexpr
  val is_int : t -> bool
  val tag : t -> int
  val field : t -> int -> t
  val set_field : t -> int -> t -> unit
  val make_block : int -> t array -> t
  val make_int : int -> t
end

(** Closures *)

type 'a arity

val arity_one : (valexpr -> valexpr Proofview.tactic) arity
val arity_suc : 'a arity -> (valexpr -> 'a) arity

val mk_closure : 'v arity -> 'v -> closure
(** The arrows in ['v] should be pure. Use [tclLIFT] or do
    [tclUNIT () >>= fun () -> f args] when you need effects. *)

val mk_closure_val : 'v arity -> 'v -> valexpr
(** Composition of [mk_closure] and [ValCls] *)

(** The proof state's environment and evar map, as [Proofview.tclENV] and [Proofview.tclEVARMAP]
    give them at the moment a direct implementation runs ([State]), or not known ([NoState]). *)
type state =
| NoState
| State of Environ.env * Evd.evar_map

(** A continuation of direct code ([Tac2interp]): [kv v] takes a value when the state is not known,
    [ks v st] a value and the [state] at the moment it is given. A continuation passed to a
    suspension gives the same as [kv v] with [ks v st] for that state or [NoState]. *)
type cont = {
  kv : valexpr -> valexpr Proofview.tactic;
  ks : valexpr -> state -> valexpr Proofview.tactic;
}

exception Suspend of (cont -> valexpr Proofview.tactic)
(** Raised by the direct run of an Ltac2 closure ([DirectRun] below) at a step that needs the
    proof monad: [Suspend s], where [s kk] is the tactic that does that step and the rest of the
    call, and gives its value to [kk]. *)

exception Tail of ((valexpr -> valexpr Proofview.tactic) -> valexpr Proofview.tactic)
(** Raised by the direct run of an Ltac2 closure at a step that needs the proof monad and ends the
    call: [Tail t], where the rest of the call with the continuation [k] is [t k]. *)

(** The direct implementation of a closure that takes the given number of arguments. For a
    primitive whose result is pure ([Tac2externals.ret]) or pure given the environment and the evar
    map ([Tac2externals.eret]): applied to that many arguments [args], the closure that carries it
    is, in the proof monad, [tclUNIT () >>= fun () -> tclUNIT (f args)] for [DirectPure (_, f)],
    and [tclUNIT () >>= fun () -> let g = f args in tclENV >>= fun env -> tclEVARMAP >>= fun sigma
    -> tclUNIT (g env sigma)] for [DirectEnv (_, f)] (the arguments are converted and passed to the
    implementation in [f args], as the closure does before it reads the environment).

    For a primitive in the proof monad ([Tac2externals.tac]) whose value is pure for some
    arguments, [DirectCheck (_, f)]: applied to that many arguments [args], the closure is
    [tclUNIT () >>= fun () -> tclUNIT v] when [f args] is [Some v], with the steps of [f args] done
    at the start of that continuation, as the closure does them; when [f args] is [None], [f] has
    done no step that the closure does not also do first (it converted the arguments only).

    For an Ltac2 closure ([Tac2interp]), [DirectRun (_, run, drun)]: when the closure is applied
    to that many arguments [args] at run time, in the continuation of a bind, [apply_val v args >>=
    k] is [run args k]. There, [drun st fuel args], with [st] the [state] at that moment and [fuel]
    the depth of subexpressions not in tail position it may still enter, does the steps that [run
    args k] does before it gives [k] a value or does a step in the proof monad, and then returns
    [v] where [run args k] then runs [k v], raises [Suspend s] where [run args k] then runs [s kk]
    for a [kk] whose both parts give [k v], or raises [Tail t] where [run args k] then runs [t k].
    Any other exception it raises, [run args k] raises after the same steps. *)
type direct =
| DirectPure of int * (valexpr list -> valexpr)
| DirectEnv of int * (valexpr list -> Environ.env -> Evd.evar_map -> valexpr)
| DirectRun of int * (valexpr list -> (valexpr -> valexpr Proofview.tactic) -> valexpr Proofview.tactic)
    * (state -> int -> valexpr list -> valexpr)
| DirectCheck of int * (valexpr list -> valexpr option)

(** The direct implementation of a closure for its number of arguments, taking them one by one
    instead of in a list, for the closures and numbers of arguments that compiled Ltac2 code calls
    most ([Tac2interp]). A closure carries [NoFast] or the entry of its own number of arguments,
    which agrees with its [direct] implementation:
    - [Pure1 f]: [f a] is [d [a]] for [DirectPure (1, d)], and so on for [Pure2] and [Pure3];
    - [Env1 f]: [f a env sigma] is [d [a] env sigma] for [DirectEnv (1, d)], and so on for [Env2];
    - [Check2 f]: [f a b] is [d [a; b]] for [DirectCheck (2, d)];
    - [Run1 f]: [f st fuel a] is [drun st fuel [a]] for [DirectRun (1, _, drun)], and so on up to
      [Run5].
    "Is" means: the same steps, in the same order, and the same value or exception. *)
type fast =
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

val mk_closure_direct : ?fast:fast -> 'v arity -> 'v -> direct -> closure
(** For internal use (Tac2externals). [mk_closure arity f], which carries [d] and [fast] (default
    [NoFast]). [d] must be the direct implementation of [f] as described above, and [fast] agree
    with [d]: the interpreter runs them instead of [f] where it can, so a [d] or [fast] that does
    not agree with [f] changes the results of Ltac2 code. *)

val closure_direct : valexpr -> direct option
(** The direct implementation that the closure [v] carries, if any, provided that applying [v] adds
    no frame at this moment ([Tac2bt.with_frame_is_identity] for an annotated closure). A closure
    that [apply] returns after a partial application carries the direct implementation of the
    closure it was made from, given the arguments it got. *)

val closure_fast : valexpr -> fast
(** The [fast] entry that the closure [v] carries, under the same test as [closure_direct], and
    [NoFast] where [closure_direct] gives [None]. After a partial application, the entry of the
    closure it was made from, given the arguments it got (or [NoFast]). *)

val annotate_closure : Tac2expr.frame -> closure -> closure
(** The closure must not be already annotated *)

val purify_closure : 'v arity -> 'v -> 'v
(** For internal use (Tac2externals). Wraps the applications of the ['v] argument
    to make it pure. *)

val to_closure : valexpr -> closure

val apply : closure -> valexpr list -> valexpr Proofview.tactic
(** Given a closure, apply it to some arguments. Handling of argument mismatches
    is done automatically, i.e. in case of over or under-application. *)

val apply_val : valexpr -> valexpr list -> valexpr Proofview.tactic
(** Composition of [to_closure] and [apply] *)

val apply_partial_val : valexpr -> valexpr list -> valexpr
(** [apply_partial_val v args], [args] fewer than the closure [v] takes: the value that [apply_val v
    args] gives in [tclUNIT], computed by the same steps. *)

val abstract : int -> (valexpr list -> valexpr Proofview.tactic) -> closure
(** Turn a fixed-arity function into a closure. The inner function is guaranteed
    to be applied to a list whose size is the integer argument. *)

val abstract_run : ?fast:fast -> int -> (valexpr list -> valexpr Proofview.tactic) ->
  (valexpr list -> (valexpr -> valexpr Proofview.tactic) -> valexpr Proofview.tactic) ->
  (state -> int -> valexpr list -> valexpr) -> closure
(** For internal use (Tac2interp). [abstract n f], which carries [DirectRun (n, run, drun)] and
    [fast] (default [NoFast]). [run], [drun] and [fast] must agree with [f] as [direct] and [fast]
    say: the interpreter runs them instead of [f] where it can. *)
