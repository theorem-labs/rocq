(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The model search of [lia] and [nia]. It runs on a cube ahead of their prover
    ([Coq_micromega.witness_list]). It develops the cube as [lia] does, so each monomial is an atom,
    and solves the rational relaxation. From its point, it tries the point itself, then its nearest,
    floor and ceiling roundings, then a depth-first branching on a fractional variable, with
    [model_lps] LPs in all. It returns a model only after it has evaluated every constraint of the
    cube exactly over Z, with the values of the cube's variables. No certificate refutes a cube that
    has an integer model, so no prover proves it. The search gives up on the cube (no model) when this
    evaluation would compute an integer of more than [model_max_bits] bits: the prover then decides
    the cube, as without the search. *)

open Polynomial
open Micromega
module Z_ = NumCompat.Z
module Q = NumCompat.Q
module Ml2C = Mutils.CamlToCoq
module C2Ml = Mutils.CoqToCaml
open Mutils

(** The number of LPs that the model search may solve, the root LP included *)
let model_lps = 16

type result =
  | Found of (int * Micromega.z) list
  | Missed
  | Deferred

(** The largest bit length of a product or power that the model search computes, and the largest
    exponent of a cube that it searches. It bounds the work of each operation (a GMP product with a
    2^16-bit result takes tens of microseconds), where an unbounded power at the LP point can cost
    minutes and gigabytes on a cube that the prover never reaches. The exponent bound also bounds the
    expansion of [p ^ n] into [n] products before the search's LP. *)
let model_max_bits = 1 lsl 16

(** Raised instead of computing an integer of more than [model_max_bits] bits, or of searching a cube
    with an exponent above [model_max_bits] *)
exception Model_too_big

let model_check_bits b = if b > model_max_bits then raise Model_too_big

(** [model_exponent p] is [p] as an int; [Model_too_big] if it exceeds [model_max_bits]. *)
let rec model_exponent p =
  let k =
    match p with
    | XH -> 1
    | XO p -> 2 * model_exponent p
    | XI p -> (2 * model_exponent p) + 1
  in
  model_check_bits k; k

(** The largest size ([model_size]) of a cube that the model search develops. The size of a power is
    the exponent times the size of its base, so nested powers below [model_max_bits] can still make a
    development of billions of products, which the search must not start on a cube the prover may
    never reach. *)
let model_max_size = 1 lsl 20

(** [model_size acc e] is [acc] plus the size of [e]: its nodes, a power [p ^ n] counting [n] times
    the size of [p] (the development of [p ^ n] is [n] products). It raises [Model_too_big] if [e] has
    an exponent above [model_max_bits] or if the size exceeds [model_max_size]. *)
let rec model_size acc e =
  let s =
    match e with
    | PEc _ | PEX _ -> acc + 1
    | PEadd (e1, e2) | PEsub (e1, e2) | PEmul (e1, e2) -> model_size (model_size (acc + 1) e1) e2
    | PEopp e -> model_size (acc + 1) e
    | PEpow (e, n) ->
      let k = match n with N0 -> 1 | Npos p -> model_exponent p in
      let s = model_size 0 e in
      (* no [k * s] beyond [model_max_size], which a 32-bit int could not hold *)
      if s > model_max_size / k then raise Model_too_big;
      acc + 1 + (k * s)
  in
  if s > model_max_size then raise Model_too_big else s

let pol_cap = model_max_size + 1

let rec pol_digits n = function
  | XH -> n
  | XO p | XI p -> if n > 21 then n else pol_digits (n + 1) p

let rec pol_degree = function
  | XH -> 1
  | XO p -> min pol_cap (2 * pol_degree p)
  | XI p -> min pol_cap ((2 * pol_degree p) + 1)

(** The deepest nesting of coefficient polynomials that [pol_size] walks: a deeper polynomial gets the
    largest size, so the walk's stack stays small whatever the polynomial. *)
let pol_max_depth = 4096

let rec pol_size_acc depth acc = function
  | Pc _ -> acc + 1
  | Pinj (_, p) -> pol_size_acc depth acc p
  | PX (p, i, q) ->
    if depth >= pol_max_depth then pol_cap
    else
      let d = if pol_digits 1 i > 21 then pol_cap else pol_degree i in
      let acc = min pol_cap (acc + 3 + d) in
      if acc >= pol_cap then pol_cap
      else pol_size_acc depth (min pol_cap (pol_size_acc (depth + 1) acc p)) q

(** [pol_size p]: about the size of the expression that [Micromega.denorm] makes of [p], as
    [model_size] counts it (a term [q * x ^ i] counting [i] for [x ^ i]), capped at [model_max_size + 1].
    A degree with more than 21 binary digits, or a nesting of coefficients deeper than
    [pol_max_depth], saturates at once, so its walk's stack is bounded. *)
let pol_size p = min pol_cap (pol_size_acc 0 0 p)

(** [model_pow v n] is [v ^ n], where [v ^ n] has at most [model_max_bits] bits. *)
let model_pow v = function
  | N0 -> Z_.one
  | Npos p ->
    let n = model_exponent p in
    (* |v| < 2^(numbits v), so v ^ n has at most n * numbits v bits *)
    model_check_bits (n * Z_.numbits v);
    Z_.power_int v n

let rec model_eval env = function
  | PEc c -> C2Ml.z_big_int c
  | PEX v -> env (C2Ml.positive v)
  | PEadd (e1, e2) -> Z_.add (model_eval env e1) (model_eval env e2)
  | PEsub (e1, e2) -> Z_.sub (model_eval env e1) (model_eval env e2)
  | PEmul (e1, e2) ->
    let v1 = model_eval env e1 in
    let v2 = model_eval env e2 in
    model_check_bits (Z_.numbits v1 + Z_.numbits v2);
    Z_.mul v1 v2
  | PEopp e -> Z_.neg (model_eval env e)
  | PEpow (e, n) -> model_pow (model_eval env e) n

let model_holds env (e, op) =
  let s = Z_.sign (model_eval env e) in
  match op with
  | Equal -> s = 0
  | NonEqual -> s <> 0
  | Strict -> s > 0
  | NonStrict -> s >= 0

let rec model_vars acc = function
  | PEc _ -> acc
  | PEX v -> ISet.add (C2Ml.positive v) acc
  | PEadd (e1, e2) | PEsub (e1, e2) | PEmul (e1, e2) ->
    model_vars (model_vars acc e1) e2
  | PEopp e | PEpow (e, _) -> model_vars acc e

(** The processor seconds per unit of cube size ([model_size]) of the last search's development, of
    its first LP, and of its check of that LP's point and roundings, in this process: the prediction
    of the next search's first step on a cube of a given size (0 before the first search; the
    early-failure check then predicts the first step from the prover's seconds). *)
let dev_rate = ref 0.
let lp_rate = ref 0.
let node_rate = ref 0.

(** [timed k f] is [f ()], and calls [k] with its processor seconds, also when [f] raises. *)
let timed k f =
  let t = Sys.time () in
  match f () with
  | v -> k (Sys.time () -. t); v
  | exception e ->
    let e = Exninfo.capture e in
    k (Sys.time () -. t);
    Exninfo.iraise e

(** [model_search affordable size sys wsys] searches an integer model of [sys], of size [size], whose
    developed form is [wsys]. Before each LP it asks [affordable] with the predicted seconds of the LP
    and of the check of its point (one step): for the first LP, from the rates of the last search and
    [size]; for a later one, from this search's last LP and check. *)
let model_search affordable size sys wsys =
  (* The LP column of a variable [x] of [sys] is its degree-1 monomial, the vector [LinPoly.var x]. A
     variable that occurs only in nonlinear monomials gets a new column, which no constraint uses:
     its value is 0. *)
  let cols =
    List.map
      (fun x -> (x, LinPoly.var x))
      (ISet.elements
         (List.fold_left (fun acc (e, _) -> model_vars acc e) ISet.empty sys))
  in
  let is_int q = Z_.equal (Q.den q) Z_.one in
  let model round vals =
    let m =
      List.fold_left
        (fun m (x, q) -> IMap.add x (Q.to_bigint (round q)) m)
        IMap.empty vals
    in
    if List.for_all (model_holds (fun x -> IMap.find x m)) sys then
      Some (Found (List.map (fun (x, v) -> (x, Ml2C.bigint v)) (IMap.bindings m)))
    else None
  in
  (* [candidate sol]: a model among the LP point [sol] and its roundings, or [Error (x, q)], [x] a
     variable whose value [q] at [sol] is fractional, to branch on *)
  let candidate sol =
    let vals = List.map (fun (x, col) -> (x, Vect.dotproduct col sol)) cols in
    match List.find_opt (fun (_, q) -> not (is_int q)) vals with
    | None -> Ok (model (fun q -> q) vals)
    | Some (x, q) -> (
      match List.find_map (fun round -> model round vals) [Q.round; Q.floor; Q.ceiling] with
      | Some _ as m -> Ok m
      | None -> Error (x, q) )
  in
  let lps = ref 0 and last_lp = ref 0. and last_node = ref 0. in
  let size = float_of_int (max 1 size) in
  let rec branch extra =
    let predicted =
      if !lps = 0 then (!lp_rate +. !node_rate) *. size else !last_lp +. !last_node
    in
    if !lps >= model_lps || not (affordable predicted) then None
    else begin
      incr lps;
      let first = !lps = 1 in
      let bounds = List.map (fun c -> WithProof.of_cstr (c, ProofFormat.Zero)) extra in
      let sol =
        timed
          (fun dt -> last_lp := dt; if first then lp_rate := dt /. size)
          (fun () -> Simplex.relaxed_point (List.rev_append bounds wsys))
      in
      match sol with
      | None -> None
      | Some sol -> (
        let c =
          timed
            (fun dt -> last_node := dt; if first then node_rate := dt /. size)
            (fun () -> candidate sol)
        in
        match c with
        | Ok m -> m
        | Error (x, q) -> (
          let col = List.assoc x cols in
          let le = {coeffs = Vect.uminus col; op = Ge; cst = Q.neg (Q.floor q)} in
          let ge = {coeffs = col; op = Ge; cst = Q.ceiling q} in
          match branch (le :: extra) with
          | Some _ as m -> m
          | None -> branch (ge :: extra) ) )
    end
  in
  match branch [] with Some r -> r | None -> Missed

let find_model ?(affordable = fun _ -> true) prfdepth sys =
  try
    let size = List.fold_left (fun acc (e, _) -> model_size acc e) 0 sys in
    let fsize = float_of_int (max 1 size) in
    if not (affordable ((!dev_rate +. !lp_rate +. !node_rate) *. fsize)) then Deferred
    else
      let wsys =
        timed
          (fun dt -> dev_rate := dt /. fsize)
          (fun () -> Certificate.develop_z_constraints prfdepth sys)
      in
      model_search affordable size sys wsys
  with
  | Model_too_big -> Missed
  | e when CErrors.noncritical e -> Missed
