(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Proofview
open Tac2ffi

(* Local shortcuts. *)
type v = Tac2val.valexpr
type 'r of_v = v -> 'r
type 'r to_v = 'r -> v
type 'a with_env = Environ.env -> Evd.evar_map -> 'a

(* We use two levels of GADT to get rid of the third type parameter, which has
   to be give for this type definition to be accepted. If we remove it, we get
   an error: "a type variable cannot be deduced from the type parameters". *)
type (_, _, _) spec_aux =
  | T : 'r to_v -> (v tactic, 'r tactic, 'r) spec_aux
  | V : 'r to_v -> (v tactic, 'r, 'r) spec_aux
  | E : 'r to_v -> (v tactic, 'r with_env, 'r) spec_aux
  | G : 'r to_v -> (v tactic, Goal.t -> 'r, 'r) spec_aux
  | F : 'a of_v * ('t, 'f, 'r) spec_aux -> (v -> 't , 'a -> 'f, 'r) spec_aux

type (_,_) spec = S : ('v,'f,'r) spec_aux -> ('v,'f) spec [@@unboxed]

let tac : type r. r repr -> (v tactic, r tactic) spec = fun r ->
  S (T (repr_of r))

let tac': type r. r to_v -> (v tactic, r tactic) spec = fun tr ->
  S (T tr)

let ret : type r. r repr -> (v tactic, r) spec = fun r ->
  S (V (repr_of r))

let ret': type r. r to_v -> (v tactic, r) spec = fun tr ->
  S (V tr)

let eret : type r. r repr -> (v tactic, r with_env) spec = fun r ->
  S (E (repr_of r))

let eret': type r. r to_v -> (v tactic, r with_env) spec = fun tr ->
  S (E tr)

let gret : type r. r repr -> (v tactic, Goal.t -> r) spec = fun r ->
  S (G (repr_of r))

let gret': type r. r to_v -> (v tactic, Goal.t -> r) spec = fun tr ->
  S (G tr)

let (@->) : type a t f. a repr -> (t,f) spec -> (v -> t, a -> f) spec =
  fun r (S ar) -> S (F (repr_to r, ar))

let (@-->): type a t f. a of_v -> (t,f) spec -> (v -> t, a -> f) spec =
  fun of_v (S ar) -> S (F (of_v, ar))

let rec interp_spec : type v f. (v,f) spec -> f -> v = fun (S ar) f ->
  let open Proofview.Notations in
  match ar with
  | T tr -> f >>= fun v -> tclUNIT (tr v)
  | V tr -> tclUNIT (tr f)
  | E tr -> tclENV >>= fun e -> tclEVARMAP >>= fun s -> tclUNIT (tr (f e s))
  | G tr -> Goal.enter_one @@ fun g -> tclUNIT (tr (f g))
  | F (tr,ar) -> fun v -> interp_spec (S ar) (f (tr v))

let rec arity_of : type v f. (v,f) spec -> v Tac2val.arity = fun (S ar) ->
  match ar with
  | F (_, T _) -> Tac2val.arity_one
  | F (_, V _) -> Tac2val.arity_one
  | F (_, E _) -> Tac2val.arity_one
  | F (_, G _) -> Tac2val.arity_one
  | F (_, ar) -> Tac2val.arity_suc (arity_of (S ar))
  | _ -> invalid_arg "Tac2def.arity_of: not a function spec"

(* The direct implementations of a [ret] or [eret] primitive (Tac2val.direct). They convert the
   arguments from left to right and pass each to [f] as soon as it is converted, as [interp_spec]
   does, and finally convert the result. [interp_spec] does the same steps in the same order: for
   [V tr] it gives [tclUNIT (tr f)], and for [E tr] it reads the environment and the evar map and
   then gives [tclUNIT (tr (f e s))]. Both are only applied to as many arguments as the spec takes. *)
let rec direct_pure : type v f r. (v, f, r) spec_aux -> f -> Tac2val.valexpr list -> Tac2val.valexpr =
  fun ar f args -> match ar, args with
  | V tr, [] -> tr f
  | F (tr, ar), a :: args -> direct_pure ar (f (tr a)) args
  | _ -> assert false

let rec direct_env : type v f r. (v, f, r) spec_aux -> f -> Tac2val.valexpr list ->
  Environ.env -> Evd.evar_map -> Tac2val.valexpr =
  fun ar f args -> match ar, args with
  | E tr, [] -> fun e s -> tr (f e s)
  | F (tr, ar), a :: args -> direct_env ar (f (tr a)) args
  | _ -> assert false

let rec spec_args : type v f r. (v, f, r) spec_aux -> int = function
  | F (_, ar) -> 1 + spec_args ar
  | V _ | E _ | T _ | G _ -> 0

let rec spec_result : type v f r. (v, f, r) spec_aux -> [ `Pure | `Env | `Monadic ] = function
  | F (_, ar) -> spec_result ar
  | V _ -> `Pure
  | E _ -> `Env
  | T _ | G _ -> `Monadic

(* The direct implementation of the primitive [f] of spec [ar] (a function spec), if it has one. *)
let direct_of : type v f r. (v, f, r) spec_aux -> f -> Tac2val.direct option = fun ar f ->
  match spec_result ar with
  | `Pure -> Some (Tac2val.DirectPure (spec_args ar, direct_pure ar f))
  | `Env -> Some (Tac2val.DirectEnv (spec_args ar, direct_env ar f))
  | `Monadic -> None

let define : type v f. _ -> (v,f) spec -> f -> unit = fun n ar v ->
  let v =
    match ar with
    | S (V tr) -> tr v
    | S (F _ as ar0) ->
      let arity = arity_of ar in
      let direct = direct_of ar0 v in
      let v = interp_spec ar v in
      let v = Tac2val.purify_closure arity v in
      let cl = match direct with
        | None -> Tac2val.mk_closure arity v
        | Some d -> Tac2val.mk_closure_direct arity v d
      in
      Tac2ffi.of_closure cl
    | _ -> invalid_arg "Tac2def.define: not a pure value"
  in
  Tac2env.define_primitive n v

let direct_args = function
  | Tac2val.DirectPure (n, _) | Tac2val.DirectEnv (n, _) | Tac2val.DirectRun (n, _, _)
  | Tac2val.DirectCheck (n, _) -> n

(* [define n ar v] with the direct implementation [d] instead of the one [ar] gives (none for a
   primitive in the proof monad). *)
let define_direct : type v f. _ -> (v,f) spec -> f -> Tac2val.direct -> unit = fun n ar v d ->
  match ar with
  | S (F _ as ar0) ->
    let () = if not (Int.equal (spec_args ar0) (direct_args d)) then
        invalid_arg "Tac2def.define_direct: arity mismatch" in
    let arity = arity_of ar in
    let v = interp_spec ar v in
    let v = Tac2val.purify_closure arity v in
    Tac2env.define_primitive n (Tac2ffi.of_closure (Tac2val.mk_closure_direct arity v d))
  | _ -> invalid_arg "Tac2def.define_direct: not a function spec"
