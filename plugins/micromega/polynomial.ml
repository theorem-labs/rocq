(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-20018                            *)
(*                                                                      *)
(************************************************************************)

open NumCompat
open Q.Notations
open Mutils
module Mc = Micromega

let max_nb_cstr = ref max_int

type var = int

let debug = false
let ( <+> ) = ( +/ )
let ( <*> ) = ( */ )

module Monomial : sig
  type t

  val const : t
  val is_const : t -> bool
  val var : var -> t
  val is_var : t -> bool
  val get_var : t -> var option
  val prod : t -> t -> t
  val factor : t -> var -> t option
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val mem : var -> t -> bool
  val pp : out_channel -> t -> unit
  val fold : (var -> int -> 'a -> 'a) -> t -> 'a -> 'a
  val sqrt : t -> t option
  val variables : t -> ISet.t
  val degree : t -> int
  val subset : t -> t -> bool
  val output : out_channel -> t -> unit
end =
struct
  type t = int array
  (* Compact representation [| d; e₀; v₀; ...; eₙ; vₙ |] where
    d = Σi v_i is the multi-degree
    e_i gives the variable number as a diff, i.e. the variable at position i
        is Σi e_i, and e_i ≠ 0 for all i > 0
    v_i is the degree of e_i, must be ≠ 0
  *)

  let const = [|0|]

  let subset m1 m2 =
    m1.(0) <= m2.(0) &&

    let len1 = Array.length m1 in
    let len2 = Array.length m2 in

    let get_var m c v =
      v+m.(c) , m.(c+1) in

    let rec xsubset cur1 v1 e1 cur2 v2 e2 =
      match Int.compare v1 v2 with
      | 0 -> e1 <= e2 &&
             (if cur1 + 2 = len1
              then true
              else if cur2 + 2 = len2
              then false
              else
                let (v1,e1) = get_var m1 (cur1+2) v1 in
                let (v2,e2) = get_var m2 (cur2+2) v2 in
                xsubset (cur1+2) v1 e1 (cur2+2) v2 e2)
      | -1 -> false
      |  _ -> if cur2 + 2 = len2
        then false
        else  let (v2,e2) = get_var m2 (cur2+2) v2 in
          xsubset cur1 v1 e1 (cur2+2) v2 e2
    in
    if len1 <= 1 then true
    else if len2 <= 1 then false
    else xsubset 1 m1.(1) m1.(2) 1 m2.(1) m2.(2)

  let is_const (m : t) = match m with [|_|] -> true | _ -> false

  let var x = [|1; x; 1|]

  let is_var (m : t) = Int.equal m.(0) 1

  let get_var (m : t) = match m with
  | [|1; x; _|] -> Some x
  | _ -> None

  let prod (m1 : t) (m2 : t) =
    let len1 = Array.length m1 in
    let len2 = Array.length m2 in
    (* Compute the number of variables in the monomial *)
    let rec nvars accu cur1 cur2 i1 i2 =
      if Int.equal i1 len1 && Int.equal i2 len2 then accu
      else if Int.equal i1 len1 then accu + (len2 - i2)
      else if Int.equal i2 len2 then accu + (len1 - i1)
      else
        let ncur1 = cur1 + m1.(i1) in
        let ncur2 = cur2 + m2.(i2) in
        if ncur1 < ncur2 then nvars (accu + 2) ncur1 cur2 (i1 + 2) i2
        else if ncur1 > ncur2 then nvars (accu + 2) cur1 ncur2 i1 (i2 + 2)
        else nvars (accu + 2) ncur1 ncur2 (i1 + 2) (i2 + 2)
    in
    let n = nvars 1 0 0 1 1 in
    let m = Array.make n 0 in
    let () = m.(0) <- m1.(0) + m2.(0) in
    (* Set the variable exponents *)
    let rec set cur cur1 cur2 i i1 i2 =
      if Int.equal i1 len1 && Int.equal i2 len2 then ()
      else if Int.equal i1 len1 then
        let ncur2 = cur2 + m2.(i2) in
        let () = m.(i) <- ncur2 - cur in
        let () = m.(i + 1) <- m2.(i2 + 1) in
        set ncur2 cur1 ncur2 (i + 2) i1 (i2 + 2)
      else if Int.equal i2 len2 then
        let ncur1 = cur1 + m1.(i1) in
        let () = m.(i) <- ncur1 - cur in
        let () = m.(i + 1) <- m1.(i1 + 1) in
        set ncur1 ncur1 cur2 (i + 2) (i1 + 2) i2
      else
        let ncur1 = cur1 + m1.(i1) in
        let ncur2 = cur2 + m2.(i2) in
        if ncur1 < ncur2 then
          let () = m.(i) <- ncur1 - cur in
          let () = m.(i + 1) <- m1.(i1 + 1) in
          set ncur1 ncur1 cur2 (i + 2) (i1 + 2) i2
        else if ncur1 > ncur2 then
          let () = m.(i) <- ncur2 - cur in
          let () = m.(i + 1) <- m2.(i2 + 1) in
          set ncur2 cur1 ncur2 (i + 2) i1 (i2 + 2)
        else
          let () = m.(i) <- ncur1 - cur in
          let () = m.(i + 1) <- m1.(i1 + 1) + m2.(i2 + 1) in
          set ncur1 ncur1 ncur2 (i + 2) (i1 + 2) (i2 + 2)
    in
    let () = set 0 0 0 1 1 1 in
    m

  (*  [factor m x] returns [None] if [x] does not appear in [m], and decreases
      its exponent by one otherwise *)
  let factor (m : t) (x : var) =
    let len = Array.length m in
    let rec factor cur i =
      if Int.equal i len then None
      else
        let ncur = cur + m.(i) in
        let k = m.(i + 1) in
        if ncur < x then factor ncur (i + 2)
        else if x < ncur then None
        else if Int.equal k 1 then
          (* Need to squeeze out the binding for x *)
          let ans = Array.make (len - 2) 0 in
          let () = ans.(0) <- m.(0) - 1 in
          let () = Array.blit m 1 ans 1 (i - 1) in
          let () = Array.blit m (i + 2) ans i (len - i - 2) in
          (* Correct the diff *)
          let () = if not (Int.equal len (i + 2)) then ans.(i) <- ans.(i) + m.(i) in
          Some ans
        else
          let ans = Array.copy m in
          let () = ans.(0) <- ans.(0) - 1 in
          let () = ans.(i + 1) <- ans.(i + 1) - 1 in
          Some ans
    in
    factor 0 1

  let compare (m1 : t) (m2 : t) = CArray.compare Int.compare m1 m2

  let equal (m1 : t) (m2 : t) =
    let len = Array.length m1 in
    Int.equal len (Array.length m2)
    &&
    let rec loop i =
      i < 0
      || (Int.equal (Array.unsafe_get m1 i) (Array.unsafe_get m2 i)
         && loop (i - 1))
    in
    loop (len - 1)

  let hash (m : t) =
    let h = ref 0 in
    for i = 0 to Array.length m - 1 do
      h := (!h * 65599) + Array.unsafe_get m i
    done;
    !h land max_int

  let rec mem_from x (m : t) len cur i =
    i < len
    &&
    let cur = cur + m.(i) in
    if cur < x then mem_from x m len cur (i + 2) else Int.equal cur x

  (* [mem x m] holds if the variable [x] occurs in [m]: it walks [m] as
     [factor] does, and holds exactly when [factor m x] is not [None]. *)
  let mem (x : var) (m : t) = mem_from x m (Array.length m) 0 1

  let sqrt (m : t) = match m with
  | [|_|] -> Some const
  | _ ->
    let m = Array.copy m in
    let len = Array.length m in
    let () = m.(0) <- m.(0) / 2 in
    let rec set i =
      if Int.equal i len then ()
      else
        let v = m.(i + 1) in
        let () = if v mod 2 = 0 then m.(i + 1) <- v / 2 else raise_notrace Exit in
        set (i + 2)
    in
    try let () = set 1 in Some m with Exit -> None

  let degree (m : t) = m.(0)

  let fold f (m : t) accu =
    let len = Array.length m in
    let rec fold accu cur i =
      if Int.equal i len then accu
      else
        let cur = cur + m.(i) in
        let accu = f cur m.(i + 1) accu in
        fold accu cur (i + 2)
    in
    fold accu 0 1

  let output o m = fold (fun v i () -> Printf.fprintf o "x%i^%i" v i) m ()


  let variables (m : t) =
    fold (fun x _ accu -> ISet.add x accu) m ISet.empty

  let pp o m =
    let pp_elt o (k, v) =
      if v = 1 then Printf.fprintf o "x%i" k else Printf.fprintf o "x%i^%i" k v
    in
    let rec pp_list o l =
      match l with
      | [] -> ()
      | [e] -> pp_elt o e
      | e :: l -> Printf.fprintf o "%a*%a" pp_elt e pp_list l
    in
    pp_list o (List.rev @@ fold (fun x v accu -> (x, v) :: accu) m [])

end

module MonMap = struct
  include Map.Make (Monomial)

  let union f =
    merge (fun x v1 v2 ->
        match (v1, v2) with
        | None, None -> None
        | Some v, None | None, Some v -> Some v
        | Some v1, Some v2 -> f x v1 v2)
end

let pp_mon o (m, i) =
  if Monomial.is_const m then
    if Q.zero =/ i then () else Printf.fprintf o "%s" (Q.to_string i)
  else if Q.one =/ i then Monomial.pp o m
  else if Q.minus_one =/ i then Printf.fprintf o "-%a" Monomial.pp m
  else if Q.zero =/ i then ()
  else Printf.fprintf o "%s*%a" (Q.to_string i) Monomial.pp m

module Poly : (* A polynomial is a map of monomials *)
              (*
    This is probably a naive implementation
    (expected to be fast enough - Rocq is probably the bottleneck)
    *The new ring contribution is using a sparse Horner representation.
    *)
sig
  type t

  val pp : out_channel -> t -> unit
  val get : Monomial.t -> t -> Q.t
  val variable : var -> t
  val add : Monomial.t -> Q.t -> t -> t
  val constant : Q.t -> t
  val product : t -> t -> t
  val addition : t -> t -> t
  val uminus : t -> t
  val fold : (Monomial.t -> Q.t -> 'a -> 'a) -> t -> 'a -> 'a
end = struct
  (*normalisation bug : 0*x ... *)
  module P = Map.Make (Monomial)
  open P

  type t = Q.t P.t

  let pp o p = P.iter (fun mn i -> Printf.fprintf o "%a + " pp_mon (mn, i)) p

  (* Get the coefficient of monomial mn *)
  let get : Monomial.t -> t -> Q.t =
   fun mn p -> try find mn p with Not_found -> Q.zero

  (* The polynomial 1.x *)
  let variable : var -> t = fun x -> add (Monomial.var x) Q.one empty

  (*The constant polynomial *)
  let constant : Q.t -> t = fun c -> add Monomial.const c empty

  (* The addition of a monomial *)

  let add : Monomial.t -> Q.t -> t -> t =
   fun mn v p ->
    if Q.sign v = 0 then p
    else
      let vl = get mn p <+> v in
      if Q.sign vl = 0 then remove mn p else add mn vl p

  (** Design choice: empty is not a polynomial
     I do not remember why ....
   **)

  (* The product by a monomial *)
  let mult : Monomial.t -> Q.t -> t -> t =
   fun mn v p ->
    if Q.sign v = 0 then constant Q.zero
    else
      fold
        (fun mn' v' res -> P.add (Monomial.prod mn mn') (v <*> v') res)
        p empty

  let addition : t -> t -> t =
   fun p1 p2 -> fold (fun mn v p -> add mn v p) p1 p2

  let product : t -> t -> t =
   fun p1 p2 -> fold (fun mn v res -> addition (mult mn v p2) res) p1 empty

  let uminus : t -> t = fun p -> map (fun v -> Q.neg v) p
  let fold = P.fold
end

type vector = Vect.t

type cstr = {coeffs : vector; op : op; cst : Q.t}

and op = Eq | Ge | Gt

exception Strict

let is_strict c = c.op = Gt
let eval_op = function Eq -> ( =/ ) | Ge -> ( >=/ ) | Gt -> ( >/ )
let string_of_op = function Eq -> "=" | Ge -> ">=" | Gt -> ">"

let compare_op o1 o2 =
  match (o1, o2) with
  | Eq, Eq -> 0
  | Eq, _ -> -1
  | _, Eq -> 1
  | Ge, Ge -> 0
  | Ge, _ -> -1
  | _, Ge -> 1
  | Gt, Gt -> 0

let output_cstr o {coeffs; op; cst} =
  Printf.fprintf o "%a %s %s" Vect.pp coeffs (string_of_op op) (Q.to_string cst)

let opMult o1 o2 =
  match (o1, o2) with Eq, _ | _, Eq -> Eq | Ge, _ | _, Ge -> Ge | Gt, Gt -> Gt

let opAdd o1 o2 =
  match (o1, o2) with Eq, x | x, Eq -> x | Gt, x | x, Gt -> Gt | Ge, Ge -> Ge

module LinPoly = struct
  (** A linear polynomial a0 + a1.x1 + ... + an.xn
      By convention, the constant a0 is the coefficient of the variable 0.
   *)

  type t = Vect.t

  module MonT = struct
    (** The monomial table. Each monomial the layer has seen has one [entry];
        the monomial is registered once its entry has an index. [quotient]
        and [product] return entries, registered or not, from caches: the
        callers register a monomial when, and in the order in which,
        [linpol_of_pol] would register it. An entry caches only what stock
        computes from its monomial, with stock's own predicates. *)
    type entry =
      { mon : Monomial.t
      ; linear : bool  (** [Monomial.is_var mon || Monomial.is_const mon] *)
      ; var : var option  (** [Monomial.get_var mon] *)
      ; mutable index : int  (** [-1] while [mon] is not registered *)
      ; mutable quotients : (var * entry) list
            (** [(x, q)]: [Monomial.factor mon x = Some q.mon] *)
      ; mutable row : int  (** the [sum_products] row that last produced it *)
      ; mutable stamp : int  (** the [sum_terms] call that last set [sum] *)
      ; mutable sum : Q.t }

    module MonH = Hashtbl.Make (Monomial)

    module IntH = Hashtbl.Make (struct
      type t = int

      let equal = Int.equal

      let hash k =
        let h = k * 0x2545F4914F6CDD1D in
        (h lxor (h lsr 32)) land max_int
    end)

    let new_entry m =
      { mon = m
      ; linear = Monomial.is_var m || Monomial.is_const m
      ; var = Monomial.get_var m
      ; index = -1
      ; quotients = []
      ; row = 0
      ; stamp = 0
      ; sum = Q.zero }

    let entries : entry MonH.t = MonH.create 256

    (** [products] maps [(i lsl 30) lor j], for the indexes [i <= j] of two
        registered monomials, to the entry of their product. *)
    let products : entry IntH.t = IntH.create 256

    (** Small indexes stay in the growable dense table; [safe_reserve] can
        leave arbitrarily large gaps, so entries beyond this bound live in a
        sparse table. *)
    let max_dense_entries = 1 lsl 20

    (** [!by_index.(i)] is the entry registered at a small index [i], or
        [no_entry] when no monomial is registered at [i].  Entries at large
        indexes are in [large_by_index].  [get_fresh] and [safe_reserve] skip
        indexes, and every registered index is below [!fresh]. *)
    let no_entry = new_entry Monomial.const

    let by_index = ref (Array.make 256 no_entry)
    let large_by_index : entry IntH.t = IntH.create 16
    let fresh = ref 0

    let reserve vr =
      if !fresh > vr then failwith (Printf.sprintf "Cannot reserve %i" vr)
      else fresh := vr + 1

    let safe_reserve vr = if !fresh > vr then () else fresh := vr + 1

    let get_fresh () =
      let vr = !fresh in
      incr fresh; vr

    let intern m =
      try MonH.find entries m
      with Not_found ->
        let e = new_entry m in
        MonH.add entries m e; e

    let register_entry e =
      if e.index < 0 then begin
        let res = !fresh in
        if res < max_dense_entries then begin
          let len = Array.length !by_index in
          if res >= len then begin
            let new_len = min max_dense_entries (max (2 * len) (res + 1)) in
            let tbl = Array.make new_len no_entry in
            Array.blit !by_index 0 tbl 0 len;
            by_index := tbl
          end;
          !by_index.(res) <- e
        end
        else
          IntH.add large_by_index res e;
        e.index <- res;
        incr fresh
      end

    let register m =
      let e = intern m in
      register_entry e; e.index

    let entry i =
      if i < 0 then raise Not_found
      else
        let tbl = !by_index in
        if i < Array.length tbl then begin
          let e = Array.unsafe_get tbl i in
          if e == no_entry then raise Not_found else e
        end
        else if i < max_dense_entries then raise Not_found
        else IntH.find large_by_index i

    let retrieve i = (entry i).mon

    (** [occurs x e] holds if [Monomial.factor e.mon x] is not [None] *)
    let occurs x e =
      match e.var with
      | Some y -> Int.equal x y
      | None -> Monomial.mem x e.mon

    (** [quotient e x] is the entry of [m] where [Monomial.factor e.mon x] is
        [Some m]; [x] must occur in [e.mon] *)
    let quotient e x =
      let rec find = function
        | (y, q) :: l -> if Int.equal x y then q else find l
        | [] ->
          let q =
            match Monomial.factor e.mon x with
            | Some m -> intern m
            | None -> assert false
          in
          e.quotients <- (x, q) :: e.quotients;
          q
      in
      find e.quotients

    (** [product e1 e2] is the entry of [e1.mon * e2.mon], for registered
        [e1] and [e2] *)
    let product e1 e2 =
      let i1 = e1.index and i2 = e2.index in
      let i, j = if i1 <= i2 then (i1, i2) else (i2, i1) in
      if j >= 1 lsl 30 then intern (Monomial.prod e1.mon e2.mon)
      else
        let key = (i lsl 30) lor j in
        try IntH.find products key
        with Not_found ->
          let e = intern (Monomial.prod e1.mon e2.mon) in
          IntH.add products key e; e

    (** The last stamp used by [sum_terms] and [sum_products]. It is never
        reset: a stamp names one call, or one row. *)
    let stamp = ref 0

    (** [sum_terms iter] is the sum of the terms [iter] gives to its argument
        [add]: the distinct entries of the terms with their summed
        coefficients, when these are not zero. Like [Poly.add], it sums the
        coefficients of one monomial and drops a zero sum. *)
    let sum_terms iter =
      incr stamp;
      let s = !stamp in
      let touched = ref [] in
      iter (fun e c ->
          if Int.equal e.stamp s then e.sum <- e.sum +/ c
          else begin
            e.stamp <- s;
            e.sum <- c;
            touched := e :: !touched
          end);
      List.fold_left
        (fun acc e ->
          if Int.equal (Q.sign e.sum) 0 then acc else (e, e.sum) :: acc)
        [] !touched

    exception Collision

    (** [sum_products l1 l2] is [Poly.product] of the polynomials [l1] and
        [l2], lists of distinct registered entries with non-zero
        coefficients: the distinct entries of the product with their
        non-zero coefficients.
        @raise Collision if two monomials of [l2] have the same product by a
        monomial of [l1]. [Poly.product] then keeps one of the two
        coefficients ([Poly.mult] overwrites), not their sum. *)
    let sum_products l1 l2 =
      sum_terms (fun add ->
          List.iter
            (fun (e1, c1) ->
              incr stamp;
              let r = !stamp in
              List.iter
                (fun (e2, c2) ->
                  let e = product e1 e2 in
                  if Int.equal e.row r then raise_notrace Collision;
                  e.row <- r;
                  add e (c1 */ c2))
                l2)
            l1)

    (** [register_all l] registers the entries of [l] that are not registered,
        in ascending [Monomial.compare] order: the order in which
        [linpol_of_pol] registers the monomials of a polynomial. *)
    let register_all l =
      if List.exists (fun (e, _) -> e.index < 0) l then
        List.iter
          (fun (e, _) -> register_entry e)
          (List.sort
             (fun (e1, _) (e2, _) -> Monomial.compare e1.mon e2.mon)
             (List.filter (fun (e, _) -> e.index < 0) l))

    let init () = ignore (register Monomial.const)

    let clear () =
      MonH.reset entries;
      IntH.reset products;
      IntH.reset large_by_index;
      Array.fill !by_index 0 (Array.length !by_index) no_entry;
      fresh := 0;
      init ()

    (** [snapshot ()] is the monomial registered at each index below [!fresh] ([None] at an index
        without one); [None] if an index is past the dense table. Two states with equal snapshots
        map every index to the same monomial. *)
    let snapshot () =
      let n = !fresh in
      if n > max_dense_entries then None
      else
        let tbl = !by_index in
        Some
          (Array.init n (fun i ->
               let e = if i < Array.length tbl then Array.unsafe_get tbl i else no_entry in
               if e == no_entry then None else Some e.mon))

    (** [same_snapshot s] holds if [snapshot ()] would be [Some s] *)
    let same_snapshot s =
      Int.equal (Array.length s) !fresh
      &&
      let tbl = !by_index in
      let rec same i =
        i < 0
        ||
        let e = if i < Array.length tbl then Array.unsafe_get tbl i else no_entry in
        (match (e == no_entry, s.(i)) with
         | true, None -> true
         | false, Some m -> m == e.mon || Int.equal (Monomial.compare m e.mon) 0
         | _ -> false)
        && same (i - 1)
      in
      same (Array.length s - 1)

    let () = init ()
  end

  let var v = Vect.set (MonT.register (Monomial.var v)) Q.one Vect.null

  let of_monomial m =
    let v = MonT.register m in
    Vect.set v Q.one Vect.null

  let linpol_of_pol p =
    Poly.fold
      (fun mon num vct ->
        let vr = MonT.register mon in
        Vect.set vr num vct)
      p Vect.null

  let pol_of_linpol v =
    Vect.fold
      (fun p vr n -> Poly.add (MonT.retrieve vr) n p)
      (Poly.constant Q.zero) v

  let rocq_poly_of_linpol cst p =
    let pol_of_mon m =
      Monomial.fold
        (fun x v p ->
          Mc.PEmul (Mc.PEpow (Mc.PEX (CamlToCoq.positive x), CamlToCoq.n v), p))
        m
        (Mc.PEc (cst Q.one))
    in
    Vect.fold
      (fun acc x v ->
        let mn = MonT.retrieve x in
        Mc.PEadd (Mc.PEmul (Mc.PEc (cst v), pol_of_mon mn), acc))
      (Mc.PEc (cst Q.zero))
      p

  let pp_var o vr =
    try Monomial.pp o (MonT.retrieve vr) (* this is a non-linear variable *)
    with Not_found -> Printf.fprintf o "v%i" vr

  let pp o p = Vect.pp_gen pp_var o p
  let constant c = if Q.sign c = 0 then Vect.null else Vect.set 0 c Vect.null

  (** [is_linear] reads every entry, zero coefficients included, as stock *)
  let is_linear p = Vect.for_all (fun v _ -> (MonT.entry v).MonT.linear) p

  let is_variable p =
    let (x, v), r = Vect.decomp_fst p in
    if Vect.is_null r && v >/ Q.zero then Monomial.get_var (MonT.retrieve x)
    else None

  (** [of_desc l] is the vector of [l], a list of entries of registered
      monomials in descending index order, with non-zero coefficients *)
  let of_desc l =
    List.fold_left (fun v (e, c) -> Vect.set e.MonT.index c v) Vect.null l

  (** [of_entries l] is [linpol_of_pol] of the polynomial [l], a list of
      distinct entries with non-zero coefficients: it registers the monomials
      of [l] as [linpol_of_pol] does, and returns their vector. *)
  let of_entries l =
    MonT.register_all l;
    match l with
    | [] -> Vect.null
    | [(e, c)] -> Vect.set e.MonT.index c Vect.null
    | _ ->
      of_desc
        (List.sort
           (fun (e1, _) (e2, _) -> Int.compare e2.MonT.index e1.MonT.index)
           l)

  (** [entries p] is the polynomial [pol_of_linpol p]: the entries of the
      monomials of [p] with their non-zero coefficients, in descending index
      order. Like [pol_of_linpol], it reads the entry of every index of [p],
      and drops a zero coefficient ([Vect.mul_add] can leave one).
      @raise Not_found if an index of [p] is not registered *)
  let entries p =
    Vect.fold
      (fun acc i c ->
        let e = MonT.entry i in
        if Int.equal (Q.sign c) 0 then acc else (e, c) :: acc)
      [] p

  (** [quotient_entries x p] is the polynomial [a] of [Poly.factorise x
      (pol_of_linpol p) = (a, b)]: the entries of its monomials with their
      summed non-zero coefficients. Like [pol_of_linpol], it reads the entry
      of every index of [p] and skips a zero coefficient.
      @raise Not_found if an index of [p] is not registered *)
  let quotient_entries x p =
    MonT.sum_terms (fun add ->
        Vect.fold
          (fun () i c ->
            let e = MonT.entry i in
            if (not (Int.equal (Q.sign c) 0)) && MonT.occurs x e then
              add (MonT.quotient e x) c)
          () p)

  (** [quotient x p] is the polynomial [a] such that [p = a.x + b] and [x]
      does not occur in [b]. It changes [MonT] as stock [factorise], that is
      [linpol_of_pol] of [a] and of [b], does: the monomials of [b] are
      monomials of [p], so only those of [a] can be new.
      @raise Not_found if an index of [p] is not registered, before it
      registers any monomial *)
  let quotient x p = of_entries (quotient_entries x p)

  (** [has_quotient x p] is [not (Vect.is_null (quotient x p))], computed without the quotient,
      and changes nothing. Monomials are distinct and division by [x] is injective on the
      monomials [x] occurs in, so [quotient_entries x p] has one entry per index of [p] with a
      non-zero coefficient and a monomial in which [x] occurs, with that coefficient; [of_entries]
      of a non-empty list of non-zero coefficients is not null, and of [[]] is [Vect.null]. It
      reads the entry of each index of [p] in [quotient_entries]'s order ([Vect.for_all] and
      [Vect.fold] both go down the list), each before looking at its coefficient, and stops after
      the first index with a non-zero coefficient and a monomial in which [x] occurs. If an index
      before that one is not registered, it raises [Not_found] there, as [quotient_entries]
      does, before any registration. If it finds one, the caller computes [quotient x p], which
      reads the same indexes again and raises [Not_found] at the same index if a later one is
      not registered. Either way the same exception comes at the same point, with nothing
      registered before it. [quotient x p] with a null result registers no monomial (those of
      [[]]) and only takes a new [MonT.sum_terms] stamp, which names that call alone and is
      never read again. *)
  let has_quotient x p =
    not
      (Vect.for_all
         (fun i c ->
           let e = MonT.entry i in
           not ((not (Int.equal (Q.sign c) 0)) && MonT.occurs x e))
         p)

  (** [is_linear_for x p] is [Vect.is_constant (quotient x p)]: the quotient
      has no monomial, or only the constant, registered at index 0. *)
  let is_linear_for x p =
    let l = quotient_entries x p in
    MonT.register_all l;
    List.for_all (fun (e, _) -> Int.equal e.MonT.index 0) l

  let search_all_linear p l =
    Vect.fold
      (fun acc x v ->
        if p v then
          match (MonT.entry x).MonT.var with
          | None -> acc
          | Some x -> if is_linear_for x l then x :: acc else acc
        else acc)
      [] l

  let min_list (l : int list) =
    match l with [] -> None | e :: l -> Some (List.fold_left min e l)

  let search_linear p l = min_list (search_all_linear p l)

  let mul_cst c p = Vect.mul c p

  (** [product p1 p2] registers the monomials of the product as
      [linpol_of_pol] does.
      @raise Not_found if an index of [p1] or [p2] is not registered, before
      it registers any monomial *)
  let product p1 p2 =
    let l1 = entries p1 in
    let l2 = entries p2 in
    match (l1, l2) with
    (* [Monomial.prod Monomial.const m] and [Monomial.prod m Monomial.const]
       are [m], so [Poly.product] scales the other polynomial. *)
    | [(e, c)], _ when Monomial.is_const e.MonT.mon ->
      of_desc (List.map (fun (e, c') -> (e, c */ c')) l2)
    | _, [(e, c)] when Monomial.is_const e.MonT.mon ->
      of_desc (List.map (fun (e, c') -> (e, c */ c')) l1)
    | _ -> (
      match MonT.sum_products l1 l2 with
      | l -> of_entries l
      | exception MonT.Collision ->
        linpol_of_pol (Poly.product (pol_of_linpol p1) (pol_of_linpol p2)))

  let addition p1 p2 = Vect.add p1 p2

  let of_vect v =
    Vect.fold
      (fun acc v vl -> addition (product (var v) (constant vl)) acc)
      Vect.null v

  let variables p =
    Vect.fold
      (fun acc v _ -> ISet.union (Monomial.variables (MonT.retrieve v)) acc)
      ISet.empty p

  let monomials p = Vect.fold (fun acc v _ -> ISet.add v acc) ISet.empty p

  let pp_goal typ o l =
    let vars =
      List.fold_left
        (fun acc p -> ISet.union acc (variables (fst p)))
        ISet.empty l
    in
    let pp_vars o i =
      ISet.iter (fun v -> Printf.fprintf o "(x%i : %s) " v typ) vars
    in
    Printf.fprintf o "forall %a\n" pp_vars vars;
    List.iteri
      (fun i (p, op) ->
        Printf.fprintf o "(H%i : %a %s 0)\n" i pp p (string_of_op op))
      l;
    Printf.fprintf o ", False\n"

  let collect_square p =
    Vect.fold
      (fun acc v _ ->
        let m = MonT.retrieve v in
        match Monomial.sqrt m with None -> acc | Some s -> MonMap.add s m acc)
      MonMap.empty p
end

module ProofFormat = struct
  type prf_rule =
    | Annot of string * prf_rule
    | Hyp of int
    | Def of int
    | Ref of int
    | Cst of Q.t
    | Zero
    | Square of Vect.t
    | MulC of Vect.t * prf_rule
    | Gcd of Z.t * prf_rule
    | MulPrf of prf_rule * prf_rule
    | AddPrf of prf_rule * prf_rule
    | CutPrf of prf_rule
    | LetPrf of prf_rule * prf_rule

  type proof =
    | Done
    | Step of int * prf_rule * proof
    | Split of int * Vect.t * proof * proof
    | Enum of int * prf_rule * Vect.t * prf_rule * proof list
    | ExProof of int * int * int * var * var * var * proof

  (* x = z - t, z >= 0, t >= 0 *)

  let rec output_prf_rule o = function
    | Annot (s, p) -> Printf.fprintf o "(%a)@%s" output_prf_rule p s
    | Hyp i -> Printf.fprintf o "Hyp %i" i
    | Def i -> Printf.fprintf o "Def %i" i
    | Ref i -> Printf.fprintf o "Ref %i" i
    | LetPrf (p1, p2) ->
      Printf.fprintf o "Let (%a) in %a" output_prf_rule p1 output_prf_rule p2
    | Cst c -> Printf.fprintf o "Cst %s" (Q.to_string c)
    | Zero -> Printf.fprintf o "Zero"
    | Square s -> Printf.fprintf o "(%a)^2" Poly.pp (LinPoly.pol_of_linpol s)
    | MulC (p, pr) ->
      Printf.fprintf o "(%a) * (%a)" Poly.pp (LinPoly.pol_of_linpol p)
        output_prf_rule pr
    | MulPrf (p1, p2) ->
      Printf.fprintf o "(%a) * (%a)" output_prf_rule p1 output_prf_rule p2
    | AddPrf (p1, p2) ->
      Printf.fprintf o "%a + %a" output_prf_rule p1 output_prf_rule p2
    | CutPrf p -> Printf.fprintf o "[%a]" output_prf_rule p
    | Gcd (c, p) -> Printf.fprintf o "(%a)/%s" output_prf_rule p (Z.to_string c)

  let rec output_proof o = function
    | Done -> Printf.fprintf o "."
    | Step (i, p, pf) ->
      Printf.fprintf o "%i:= %a\n ; %a" i output_prf_rule p output_proof pf
    | Split (i, v, p1, p2) ->
      Printf.fprintf o "%i:=%a ; { %a } { %a }" i Vect.pp v output_proof p1
        output_proof p2
    | Enum (i, p1, v, p2, pl) ->
      Printf.fprintf o "%i{%a<=%a<=%a}%a" i output_prf_rule p1 Vect.pp v
        output_prf_rule p2 (pp_list ";" output_proof) pl
    | ExProof (i, j, k, x, z, t, pr) ->
      Printf.fprintf o "%i := %i = %i - %i ; %i := %i >= 0 ; %i := %i >= 0 ; %a"
        i x z t j z k t output_proof pr

  module OrdPrfRule = struct
    type t = prf_rule

    let id_of_constr = function
      | Annot _ -> 0
      | Hyp _ -> 1
      | Def _ -> 2
      | Ref _ -> 3
      | Cst _ -> 4
      | Zero -> 5
      | Square _ -> 6
      | MulC _ -> 7
      | Gcd _ -> 8
      | MulPrf _ -> 9
      | AddPrf _ -> 10
      | CutPrf _ -> 11
      | LetPrf _ -> 12

    let cmp_pair c1 c2 (x1, x2) (y1, y2) =
      match c1 x1 y1 with 0 -> c2 x2 y2 | i -> i

    let rec compare p1 p2 =
      match (p1, p2) with
      | Annot (s1, p1), Annot (s2, p2) ->
        if s1 = s2 then compare p1 p2 else String.compare s1 s2
      | Hyp i, Hyp j -> Int.compare i j
      | Def i, Def j -> Int.compare i j
      | Ref i, Ref j -> Int.compare i j
      | Cst n, Cst m -> Q.compare n m
      | Zero, Zero -> 0
      | Square v1, Square v2 -> Vect.compare v1 v2
      | MulC (v1, p1), MulC (v2, p2) ->
        cmp_pair Vect.compare compare (v1, p1) (v2, p2)
      | Gcd (b1, p1), Gcd (b2, p2) ->
        cmp_pair Z.compare compare (b1, p1) (b2, p2)
      | MulPrf (p1, q1), MulPrf (p2, q2) ->
        cmp_pair compare compare (p1, q1) (p2, q2)
      | AddPrf (p1, q1), AddPrf (p2, q2) ->
        cmp_pair compare compare (p1, q1) (p2, q2)
      | CutPrf p, CutPrf p' -> compare p p'
      | LetPrf(p1,q1) , LetPrf(p2,q2) ->
        cmp_pair compare compare (p1, q1) (p2, q2)
      | _, _ -> Int.compare (id_of_constr p1) (id_of_constr p2)
  end

  module PrfRuleMap = Map.Make (OrdPrfRule)

  let rec pr_size = function
    | Annot (_, p) -> pr_size p
    | Zero | Square _ -> Q.zero
    | Hyp _ -> Q.one
    | Def _ -> Q.one
    | Ref _ -> Q.one
    | Cst n -> n
    | Gcd (i, p) -> pr_size p // Q.of_bigint i
    | MulPrf (p1, p2) | AddPrf (p1, p2) | LetPrf (p1, p2) ->
      pr_size p1 +/ pr_size p2
    | CutPrf p -> pr_size p
    | MulC (v, p) -> pr_size p

  let rec pr_unit  = function
    | Annot (_, p) -> pr_unit p
    | Zero | Square _ -> true
    | Hyp _ -> true
    | Def _ -> true
    | Cst n -> true
    | _ -> false

  let rec pr_rule_max_hyp = function
    | Annot (_, p) -> pr_rule_max_hyp p
    | Hyp i -> i
    | Def i -> -1
    | Ref i -> -1
    | Cst _ | Zero | Square _ -> -1
    | MulC (_, p) | CutPrf p | Gcd (_, p) -> pr_rule_max_hyp p
    | MulPrf (p1, p2) | AddPrf (p1, p2) | LetPrf (p1, p2) ->
      max (pr_rule_max_hyp p1) (pr_rule_max_hyp p2)

  let rec pr_rule_max_def = function
    | Annot (_, p) -> pr_rule_max_hyp p
    | Hyp i -> -1
    | Def i -> i
    | Ref _ -> -1
    | Cst _ | Zero | Square _ -> -1
    | MulC (_, p) | CutPrf p | Gcd (_, p) -> pr_rule_max_def p
    | MulPrf (p1, p2) | AddPrf (p1, p2) | LetPrf (p1, p2) ->
      max (pr_rule_max_def p1) (pr_rule_max_def p2)

  let rec proof_max_def = function
    | Done -> -1
    | Step (i, pr, prf) -> max i (max (pr_rule_max_def pr) (proof_max_def prf))
    | Split (i, _, p1, p2) -> max i (max (proof_max_def p1) (proof_max_def p2))
    | Enum (i, p1, _, p2, l) ->
      let m = max (pr_rule_max_def p1) (pr_rule_max_def p2) in
      List.fold_left (fun i prf -> max i (proof_max_def prf)) (max i m) l
    | ExProof (i, j, k, _, _, _, prf) ->
      max (max (max i j) k) (proof_max_def prf)

  (** [pr_rule_def_cut id pr] gives an explicit [id] to cut rules.
      This is because the Rocq proof format only accept they as a proof-step *)
  let pr_rule_def_cut m id p =
    let rec pr_rule_def_cut m id = function
      | Annot (_, p) -> pr_rule_def_cut m id p
      | MulC (p, prf) ->
        let bds, m, id', prf' = pr_rule_def_cut m id prf in
        (bds, m, id', MulC (p, prf'))
      | MulPrf (p1, p2) ->
        let bds1, m, id, p1 = pr_rule_def_cut m id p1 in
        let bds2, m, id, p2 = pr_rule_def_cut m id p2 in
        (bds2 @ bds1, m, id, MulPrf (p1, p2))
      | AddPrf (p1, p2) ->
        let bds1, m, id, p1 = pr_rule_def_cut m id p1 in
        let bds2, m, id, p2 = pr_rule_def_cut m id p2 in
        (bds2 @ bds1, m, id, AddPrf (p1, p2))
      | LetPrf (p1, p2) ->
        let bds1, m, id, p1 = pr_rule_def_cut m id p1 in
        let bds2, m, id, p2 = pr_rule_def_cut m id p2 in
        (bds2 @ bds1, m, id, LetPrf (p1, p2))
      | CutPrf p | Gcd (_, p) -> (
        let bds, m, id, p = pr_rule_def_cut m id p in
        try
          let id' = PrfRuleMap.find p m in
          (bds, m, id, Def id')
        with Not_found ->
          let m = PrfRuleMap.add p id m in
          ((id, p) :: bds, m, id + 1, Def id) )
      | (Square _ | Cst _ | Def _ | Hyp _ | Ref _ | Zero) as x -> ([], m, id, x)
    in
    pr_rule_def_cut m id p

  (* Do not define top-level cuts *)
  let pr_rule_def_cut m id = function
    | CutPrf p ->
      let bds, m, ids, p' = pr_rule_def_cut m id p in
      (bds, m, ids, CutPrf p')
    | p -> pr_rule_def_cut m id p

  let rec implicit_cut p = match p with CutPrf p -> implicit_cut p | _ -> p

  let rec pr_rule_collect_defs pr =
    match pr with
    | Annot (_, pr) -> pr_rule_collect_defs pr
    | Def i -> ISet.add i ISet.empty
    | Hyp i -> ISet.empty
    | Ref i -> ISet.empty
    | Cst _ | Zero | Square _ -> ISet.empty
    | MulC (_, pr) | Gcd (_, pr) | CutPrf pr -> pr_rule_collect_defs pr
    | MulPrf (p1, p2) | AddPrf (p1, p2) | LetPrf (p1, p2) ->
      ISet.union (pr_rule_collect_defs p1) (pr_rule_collect_defs p2)


  let add_proof x y =
    match (x, y) with Zero, p | p, Zero -> p | _ -> AddPrf (x, y)

  let rec mul_cst_proof c p =
    match p with
    | Annot (s, p) -> Annot (s, mul_cst_proof c p)
    | MulC (v, p') -> MulC (Vect.mul c v, p')
    | _ -> (
      match Q.sign c with
      | 0 -> Zero (* This is likely to be a bug *)
      | -1 ->
        MulC (LinPoly.constant c, p) (* [p] should represent an equality *)
      | 1 -> if Q.one =/ c then p else MulPrf (Cst c, p)
      | _ -> assert false )

  let sMulC v p =
    let c, v' = Vect.decomp_cst v in
    if Vect.is_null v' then mul_cst_proof c p else MulC (v, p)

  let mul_proof p1 p2 =
    match (p1, p2) with
    | Zero, _ | _, Zero -> Zero
    | Cst c, p | p, Cst c -> mul_cst_proof c p
    | _, _ -> MulPrf (p1, p2)

  let prf_rule_of_map m =
    PrfRuleMap.fold (fun k v acc -> add_proof (sMulC v k) acc) m Zero

  let rec dev_prf_rule p =
    match p with
    | Annot (s, p) -> dev_prf_rule p
    | Hyp _ | Def _ | Ref _ | Cst _ | Zero | Square _ ->
      PrfRuleMap.singleton p (LinPoly.constant Q.one)
    | MulC (v, p) ->
      PrfRuleMap.map (fun v1 -> LinPoly.product v v1) (dev_prf_rule p)
    | AddPrf (p1, p2) ->
      PrfRuleMap.merge
        (fun k o1 o2 ->
          match (o1, o2) with
          | None, None -> None
          | None, Some v | Some v, None -> Some v
          | Some v1, Some v2 -> Some (LinPoly.addition v1 v2))
        (dev_prf_rule p1) (dev_prf_rule p2)
    | MulPrf (p1, p2) -> (
      let p1' = dev_prf_rule p1 in
      let p2' = dev_prf_rule p2 in
      let p1'' = prf_rule_of_map p1' in
      let p2'' = prf_rule_of_map p2' in
      match p1'' with
      | Cst c -> PrfRuleMap.map (fun v1 -> Vect.mul c v1) p2'
      | _ -> PrfRuleMap.singleton (MulPrf (p1'', p2'')) (LinPoly.constant Q.one)
      )
    | Gcd (c, p) ->
      PrfRuleMap.singleton
        (Gcd (c, prf_rule_of_map (dev_prf_rule p)))
        (LinPoly.constant Q.one)
    | CutPrf p ->
      PrfRuleMap.singleton
        (CutPrf (prf_rule_of_map (dev_prf_rule p)))
        (LinPoly.constant Q.one)
    | LetPrf (p1, p2) ->
      let p1' = dev_prf_rule p1 in
      let p2' = dev_prf_rule p2 in
      let p1'' = prf_rule_of_map p1' in
      let p2'' = prf_rule_of_map p2' in
      PrfRuleMap.singleton (LetPrf (p1'', p2'')) (LinPoly.constant Q.one)

  (** [simplify_prf_rule p] is [prf_rule_of_map (dev_prf_rule p)]. It is idempotent, and applied
      to one of its values it registers no monomial. Write [S], [D], [M] for these three functions
      and [1] for [LinPoly.constant Q.one].
      - The values of [D p] have no zero coefficient: [1], [LinPoly.product] (its [entries] and
        [MonT.sum_terms] drop zeros), [LinPoly.addition] ([Vect.add] drops zero sums) and
        [Vect.mul c] ([] when [c] is 0).
      - The keys of [D p] are atoms ([Hyp], [Def], [Ref], [Cst], [Zero], [Square]), [MulPrf (S
        p1, S p2)] with [S p1] not a [Cst], [Gcd (c, S p1)], [CutPrf (S p1)] and [LetPrf (S p1, S
        p2)], for subterms [p1], [p2] of [p]; by induction on [p], [D k = {k -> 1}] for each key
        [k]: for [MulPrf], [D] computes [S (S p1) = S p1], not a [Cst], and [S (S p2) = S p2].
      - For a key [k] and such a value [v], the term [t = sMulC v k] of [M] is [Zero] when [v] is
        null, or is [1] with [k = Zero]; otherwise [D t = {k -> v}]: [MulC (v, k)] for [v] not
        constant ([product v 1] is [v], scaled by 1), [k] for [v = 1], [MulPrf (Cst c, k)] for [v
        = c > 0] ([D] scales [{k -> 1}] by [c]) and [MulC (c, k)] for [v = c < 0] ([product c 1 =
        c]). These products take [LinPoly.product]'s cases for a constant factor, which register
        nothing ([of_desc]).
      - [M m] adds the terms that are not [Zero], in the order of the keys ([add_proof] drops a
        [Zero]). [D] of that sum is [m] without the entries whose term is [Zero] (or [{Zero ->
        1}] if all are, whose term is [Zero] again), and [M] of it adds the same terms in the
        same order. So [S (S p) = S p]. *)
  let simplify_prf_rule p = prf_rule_of_map (dev_prf_rule p)

  (** [simplify_proof p] removes proof steps that are never re-used. *)
  let rec simplify_proof p =
    match p with
    | Done -> (Done, ISet.empty)
    | Step (i, pr, Done) -> (p, ISet.add i (pr_rule_collect_defs pr))
    | Step (i, pr, prf) ->
      let prf', hyps = simplify_proof prf in
      if not (ISet.mem i hyps) then (prf', hyps)
      else
        ( Step (i, pr, prf')
        , ISet.add i (ISet.union (pr_rule_collect_defs pr) hyps) )
    | Split (i, v, p1, p2) ->
      let p1, h1 = simplify_proof p1 in
      let p2, h2 = simplify_proof p2 in
      if not (ISet.mem i h1) then (p1, h1) (* Should not have computed p2 *)
      else if not (ISet.mem i h2) then (p2, h2)
      else (Split (i, v, p1, p2), ISet.add i (ISet.union h1 h2))
    | Enum (i, p1, v, p2, pl) ->
      let pl, hl = List.split (List.map simplify_proof pl) in
      let hyps = List.fold_left ISet.union ISet.empty hl in
      ( Enum (i, p1, v, p2, pl)
      , ISet.add i
          (ISet.union
             (ISet.union (pr_rule_collect_defs p1) (pr_rule_collect_defs p2))
             hyps) )
    | ExProof (i, j, k, x, z, t, prf) ->
      let prf', hyps = simplify_proof prf in
      if
        (not (ISet.mem i hyps))
        && (not (ISet.mem j hyps))
        && not (ISet.mem k hyps)
      then (prf', hyps)
      else
        ( ExProof (i, j, k, x, z, t, prf')
        , ISet.add i (ISet.add j (ISet.add k hyps)) )

  let rec normalise_proof id prf =
    match prf with
    | Done -> (id, Done)
    | Step (i, Gcd (c, p), Done) -> normalise_proof id (Step (i, p, Done))
    | Step (i, p, prf) ->
      let bds, m, id, p' =
        pr_rule_def_cut PrfRuleMap.empty id (simplify_prf_rule p)
      in
      let id, prf = normalise_proof id prf in
      let prf =
        List.fold_left
          (fun acc (i, p) -> Step (i, CutPrf p, acc))
          (Step (i, p', prf))
          bds
      in
      (id, prf)
    | Split (i, v, p1, p2) ->
      let id, p1 = normalise_proof id p1 in
      let id, p2 = normalise_proof id p2 in
      (id, Split (i, v, p1, p2))
    | ExProof (i, j, k, x, z, t, prf) ->
      let id, prf = normalise_proof id prf in
      (id, ExProof (i, j, k, x, z, t, prf))
    | Enum (i, p1, v, p2, pl) ->
      (* Why do I have  top-level cuts ? *)
      (* let p1 = implicit_cut p1 in
         let p2 = implicit_cut p2 in
         let (ids,prfs) = List.split (List.map (normalise_proof id) pl) in
           (List.fold_left max  0 ids ,
              Enum(i,p1,v,p2,prfs))
      *)
      let bds1, m, id, p1' =
        pr_rule_def_cut PrfRuleMap.empty id (implicit_cut p1)
      in
      let bds2, m, id, p2' = pr_rule_def_cut m id (implicit_cut p2) in
      let ids, prfs = List.split (List.map (normalise_proof id) pl) in
      ( List.fold_left max 0 ids
      , List.fold_left
          (fun acc (i, p) -> Step (i, CutPrf p, acc))
          (Enum (i, p1', v, p2', prfs))
          (bds2 @ bds1) )

  let normalise_proof id prf =
    let prf = fst (simplify_proof prf) in
    let res = normalise_proof id prf in
    if debug then
      Printf.printf "normalise_proof %a -> %a" output_proof prf output_proof
        (snd res);
    res

  (*
  let mul_proof p1 p2 =
    let res = mul_proof p1 p2 in
    Printf.printf "mul_proof %a %a = %a\n"
    output_prf_rule p1 output_prf_rule p2 output_prf_rule res; res

  let add_proof p1 p2 =
    let res = add_proof p1 p2 in
    Printf.printf "add_proof %a %a = %a\n"
    output_prf_rule p1 output_prf_rule p2 output_prf_rule res; res


  let sMulC v p =
    let res = sMulC v p in
    Printf.printf "sMulC %a %a = %a\n" Vect.pp v output_prf_rule p output_prf_rule res ;
    res

  let mul_cst_proof c p  =
    let res = mul_cst_proof c p in
    Printf.printf "mul_cst_proof %s %a = %a\n" (Num.string_of_num c) output_prf_rule p output_prf_rule res ;
    res
 *)

  let proof_of_farkas env vect =
    Vect.fold
      (fun prf x n -> add_proof (mul_cst_proof n (IMap.find x env)) prf)
      Zero vect

  module Env :
  sig
    type t
    val make : int -> t
    val id_of_def : int -> t -> int
    val id_of_hyp : int -> t -> int
    val push_ref : t -> t
    val push_def : int -> t -> t
  end =
  struct

    (* Environments are of the form refs @ defs @ hyps *)
    type t =
      {
        lref  : int;
        ndefs : int; (* Size of ldefs *)
        ldefs : int Int.Map.t;
        nhyps : int;
      }

    let push_ref { nhyps; ndefs; lref; ldefs } =
      { nhyps; ndefs; lref = lref + 1; ldefs }

    let push_def i { nhyps; ndefs; lref; ldefs } =
      let () = if lref <> 0 then failwith "Cannot push def" in
      { nhyps; ndefs = ndefs + 1; lref; ldefs = Int.Map.add i ndefs ldefs }

    let make n = { nhyps = n; ndefs = 0; lref = 0; ldefs = Int.Map.empty }

    let id_of_def def { nhyps; ndefs; lref; ldefs } =
      try
        let pos = Int.Map.find def ldefs in
        lref + (ndefs - pos - 1)
      with Not_found -> failwith "Cannot find def"

    let id_of_hyp h { nhyps; ndefs; lref; ldefs } =
      if 0 <= h && h < nhyps then lref + ndefs + h
      else failwith "Cannot find hyp"

  end


  let cmpl_prf_rule norm (cst : Q.t -> 'a) env prf =
    let rec cmpl env = function
      | Annot (s, p) -> cmpl env p
      | Ref i -> Mc.PsatzIn (CamlToCoq.nat i)
      | Hyp h -> Mc.PsatzIn (CamlToCoq.nat (Env.id_of_hyp h env))
      | Def d -> Mc.PsatzIn (CamlToCoq.nat (Env.id_of_def d env))
      | Cst i -> Mc.PsatzC (cst i)
      | Zero -> Mc.PsatzZ
      | MulPrf (p1, p2) -> Mc.PsatzMulE (cmpl env p1, cmpl env p2)
      | AddPrf (p1, p2) -> Mc.PsatzAdd (cmpl env p1, cmpl env p2)
      | LetPrf (p1, p2) -> Mc.PsatzLet (cmpl env p1, cmpl (Env.push_ref env) p2)
      | MulC (lp, p) ->
        let lp = norm (LinPoly.rocq_poly_of_linpol cst lp) in
        Mc.PsatzMulC (lp, cmpl env p)
      | Square lp -> Mc.PsatzSquare (norm (LinPoly.rocq_poly_of_linpol cst lp))
      | _ -> failwith "Cuts should already be compiled"
    in
    cmpl env prf

  let cmpl_prf_rule_z env r =
    cmpl_prf_rule Mc.normZ (fun x -> CamlToCoq.bigint (Q.num x)) env r

  let cmpl_pol_z lp =
    try
      let cst x = CamlToCoq.bigint (Q.num x) in
      Mc.normZ (LinPoly.rocq_poly_of_linpol cst lp)
    with x ->
      Printf.printf "cmpl_pol_z %s %a\n" (Printexc.to_string x) LinPoly.pp lp;
      raise x

  let rec cmpl_proof env prf =
    match prf with
    | Done -> Mc.DoneProof
    | Step (i, p, prf) -> (
      match p with
      | CutPrf p' ->
        Mc.CutProof (cmpl_prf_rule_z env p', cmpl_proof (Env.push_def i env) prf)
      | _ -> Mc.RatProof (cmpl_prf_rule_z env p, cmpl_proof (Env.push_def i  env) prf)
      )
    | Split (i, v, p1, p2) ->
      Mc.SplitProof
        ( cmpl_pol_z v
        , cmpl_proof (Env.push_def i env) p1
        , cmpl_proof (Env.push_def i env) p2 )
    | Enum (i, p1, _, p2, l) ->
      Mc.EnumProof
        ( cmpl_prf_rule_z env p1
        , cmpl_prf_rule_z env p2
        , List.map (cmpl_proof (Env.push_def i env)) l )
    | ExProof (i, j, k, x, _, _, prf) ->
      Mc.ExProof
        (CamlToCoq.positive x, cmpl_proof (Env.push_def i  (Env.push_def j (Env.push_def k env))) prf)

  let compile_proof env prf =
    let id = 1 + proof_max_def prf in
    let _, prf = normalise_proof id prf in
    cmpl_proof env prf

end

module WithProof = struct
  type t = (LinPoly.t * op) * ProofFormat.prf_rule

  let repr p = p

  let proof p = snd p

  let polynomial ((p, _), _) = p

  (* The comparison ignores proofs on purpose *)
  let compare : t -> t -> int =
   fun ((lp1, o1), _) ((lp2, o2), _) ->
    let c = Vect.compare lp1 lp2 in
    if c = 0 then compare_op o1 o2 else c

  let annot s (p, prf) = (p, ProofFormat.Annot (s, prf))

  let output o ((lp, op), prf) =
    Printf.fprintf o "%a %s 0 by %a\n" LinPoly.pp lp (string_of_op op)
      ProofFormat.output_prf_rule prf

  let output_sys o l = List.iter (Printf.fprintf o "%a\n" output) l

  exception InvalidProof

  let zero = ((Vect.null, Eq), ProofFormat.Zero)
  let const n = ((LinPoly.constant n, Ge), ProofFormat.Cst n)
  let of_cstr (c, prf) = ((Vect.set 0 (Q.neg c.cst) c.coeffs, c.op), prf)

  let product : t -> t -> t =
   fun ((p1, o1), prf1) ((p2, o2), prf2) ->
    ((LinPoly.product p1 p2, opMult o1 o2), ProofFormat.mul_proof prf1 prf2)

  let addition : t -> t -> t =
   fun ((p1, o1), prf1) ((p2, o2), prf2) ->
    ((Vect.add p1 p2, opAdd o1 o2), ProofFormat.add_proof prf1 prf2)

  let neg : t -> t =
   fun ((p1, o1), prf1) ->
    match o1 with
    | Eq ->
      ((Vect.mul Q.minus_one p1, o1), ProofFormat.mul_cst_proof Q.minus_one prf1)
    | _ -> failwith "neg: invalid proof"

  let mul_cst c ((p1, o1), prf1) =
    let () = match o1 with
    | Eq -> ()
    | Gt | Ge -> assert (c >/ Q.zero)
    in
    let p = LinPoly.mul_cst c p1 in
    let prf = ProofFormat.mul_cst_proof c prf1 in
    ((p, o1), prf)

  let mult p ((p1, o1), prf1) =
    match o1 with
    | Eq -> ((LinPoly.product p p1, o1), ProofFormat.sMulC p prf1)
    | Gt | Ge ->
      let n, r = Vect.decomp_cst p in
      if Vect.is_null r && n >/ Q.zero then
        ((LinPoly.product p p1, o1), ProofFormat.mul_cst_proof n prf1)
      else (
        if debug then
          Printf.printf "mult_error %a [*] %a\n" LinPoly.pp p output
            ((p1, o1), prf1);
        raise InvalidProof )

  let def p op i = ((p, op), ProofFormat.Def i)

  let mkhyp p op i = ((p, op), ProofFormat.Hyp i)

  let square p q = ((p, Ge), ProofFormat.Square q)

  (** [cut (p, o)] is the constraint of [cutting_plane ((p, o), prf)], whose proof is
      [ProofFormat.CutPrf prf]: [cutting_plane] reads only [p] and [o]. *)
  let cut (p, o) =
    let c, p' = Vect.decomp_cst p in
    let g = Vect.gcd p' in
    if Z.equal Z.one g || c =/ Q.zero || not (Z.equal (Q.den c) Z.one) then None
      (* Nothing to do *)
    else
      let c1 = c // Q.of_bigint g in
      let c1' = Q.floor c1 in
      if c1 =/ c1' then None
      else
        match o with
        | Eq -> Some (Vect.set 0 Q.minus_one Vect.null, Eq)
        | Gt -> failwith "cutting_plane ignore strict constraints"
        | Ge ->
          (* This is a non-trivial common divisor *)
          Some (Vect.set 0 c1' (Vect.div (Q.of_bigint g) p), o)

  let cutting_plane (c, prf) =
    match cut c with None -> None | Some c' -> Some (c', ProofFormat.CutPrf prf)

  let construct_sign p =
    let c, p' = Vect.decomp_cst p in
    if Vect.is_null p' then
      Some
        ( match Q.sign c with
        | 0 -> (true, Eq, ProofFormat.Zero)
        | 1 -> (true, Gt, ProofFormat.Cst c)
        | _ (*-1*) -> (false, Gt, ProofFormat.Cst (Q.neg c)) )
    else None

  let get_sign l p =
    match construct_sign p with
    | None -> (
      try
        let (p', o), prf =
          List.find (fun ((p', o), prf) -> Vect.equal p p') l
        in
        Some (true, o, prf)
      with Not_found -> (
        let p = Vect.uminus p in
        try
          let (p', o), prf =
            List.find (fun ((p', o), prf) -> Vect.equal p p') l
          in
          Some (false, o, prf)
        with Not_found -> None ) )
    | Some s -> Some s

  let mult_sign : bool -> t -> t =
   fun b ((p, o), prf) -> if b then ((p, o), prf) else ((Vect.uminus p, o), prf)

  (** [pivot_by sys pc1 a1 x pc2], with [a1 = LinPoly.quotient x lp1], is stock's [linear_pivot
      sys pc1 x pc2] before the simplification of its proof. Stock computed [a1] again at each
      step of the recursion; once its monomials are registered (by the first computation),
      [LinPoly.quotient x lp1] registers nothing (its entries are registered and [MonT.quotient]
      caches its own result) and returns the same vector, so the steps reuse the first. *)
  let rec pivot_by sys ((lp1, op1), prf1) a1 x ((lp2, op2), prf2) =
    (* lp2 = a2.x + b2 *)
    let a2 = LinPoly.quotient x lp2 in
    if Vect.is_null a2 then (* We are done *)
      Some ((lp2, op2), prf2)
    else
      match (op1, op2) with
      | Eq, (Ge | Gt) -> (
        match get_sign sys a1 with
        | None -> None (* Impossible to pivot without sign information *)
        | Some (b, o, prf) ->
          let sa1 = mult_sign b ((a1, o), prf) in
          let sa2 = if b then Vect.uminus a2 else a2 in
          let (lp2, op2), prf2 =
            addition
              (product sa1 ((lp2, op2), prf2))
              (mult sa2 ((lp1, op1), prf1))
          in
          pivot_by sys ((lp1, op1), prf1) a1 x ((lp2, op2), prf2) )
      | Eq, Eq ->
        let (lp2, op2), prf2 =
          addition
            (mult a1 ((lp2, op2), prf2))
            (mult (Vect.uminus a2) ((lp1, op1), prf1))
        in
        pivot_by sys ((lp1, op1), prf1) a1 x ((lp2, op2), prf2)
      | (Ge | Gt), (Ge | Gt) -> (
        match (get_sign sys a1, get_sign sys a2) with
        | Some (b1, o1, p1), Some (b2, o2, p2) ->
          if b1 <> b2 then
            let (lp2, op2), prf2 =
              addition
                (product (mult_sign b1 ((a1, o1), p1)) ((lp2, op2), prf2))
                (product (mult_sign b2 ((a2, o2), p2)) ((lp1, op1), prf1))
            in
            pivot_by sys ((lp1, op1), prf1) a1 x ((lp2, op2), prf2)
          else None
        | _ -> None )
      | (Ge | Gt), Eq -> failwith "pivot: equality as second argument"

  let linear_pivot sys ((lp1, op1), prf1) x ((lp2, op2), prf2) =
    (* lp1 = a1.x + b1 *)
    let a1 = LinPoly.quotient x lp1 in
    match pivot_by sys ((lp1, op1), prf1) a1 x ((lp2, op2), prf2) with
    | None -> None
    | Some (c, p) -> Some (c, ProofFormat.simplify_prf_rule p)

  let is_substitution strict ((p, o), prf) =
    let pred v = if strict then v =/ Q.one || v =/ Q.minus_one else true in
    match o with Eq -> LinPoly.search_linear pred p | _ -> None

  let sort (sys : t list) =
    let size ((p, o), prf) =
      let _, p' = Vect.decomp_cst p in
      let (x, q), p' = Vect.decomp_fst p' in
      Vect.fold
        (fun (l, (q, x)) x' q' ->
          let q' = Q.abs q' in
          (l + 1, if q </ q then (q, x) else (q', x')))
        (1, (Q.abs q, x))
        p
    in
    let cmp ((l1, (q1, _)), ((_, o), _)) ((l2, (q2, _)), ((_, o'), _)) =
      if l1 < l2 then -1 else if l1 = l2 then Q.compare q1 q2 else 1
    in
    List.sort cmp (List.rev_map (fun wp -> (size wp, wp)) sys)

  (** [step sys0 v pc a1 (c, n)]: the result of a round of [iterate_pivot] (below) on the
      constraint [c], with flag [n], for the round's variable [v], equation [pc] and quotient
      [a1] (computed when first forced) *)
  let step sys0 v pc a1 ((((lp2, op2), prf2) as c), n) =
    let a1 = Lazy.force a1 in
    if not (LinPoly.has_quotient v lp2) then
      if n then Some (c, true) else Some (((lp2, op2), ProofFormat.simplify_prf_rule prf2), true)
    else
      match pivot_by sys0 pc a1 v c with
      | None -> None
      | Some (c, prf) -> Some ((c, ProofFormat.simplify_prf_rule prf), true)

  (** Stock's [iterate_pivot p sys0] was, with [extract], [simplify] and [iterate_until_stable]
      from Mutils:
      {[
        let elim sys =
          match extract p sys with
          | None, _ -> None
          | Some (v, pc), sys' -> simplify (linear_pivot sys0 pc v) sys'
        in
        iterate_until_stable elim (List.map snd (sort sys0))
      ]}
      It is computed here on the same lists with the same functions, each constraint carrying a
      flag [n]: its proof is a value of [ProofFormat.simplify_prf_rule], so that
      [simplify_prf_rule] returns it unchanged (see [simplify_prf_rule]: it is idempotent, and on
      such a proof it registers no monomial). Three steps of [linear_pivot sys0 pc v c] change:
      - [a1 = LinPoly.quotient v lp1] is computed once per round, when the first constraint is
        pivoted, where the first call computed it (see [pivot_by]); with no constraint to pivot
        it is not computed, as stock.
      - When [v] does not occur in [c] ([LinPoly.has_quotient], which raises where the quotient
        would), stock returned [c] with [simplify_prf_rule] of its proof; this returns [c] itself
        when [n] holds (the same constraint), and the simplified proof otherwise, as stock.
      - Otherwise this is [linear_pivot]: [pivot_by] with the round's [a1].
      Each result is [Some] exactly when stock's is, so [simplify] and [iterate_until_stable] stop
      where they stopped, and the constraints come in stock's order with stock's polynomials,
      operators and proofs; the monomials are registered in stock's order, at the same indexes. *)
  let iterate_pivot p sys0 =
    let elim sys =
      let oeq, sys' = extract (fun (c, _) -> p c) sys in
      match oeq with
      | None -> None
      | Some (v, (pc, _)) ->
        let ((lp1, _), _) = pc in
        let a1 = lazy (LinPoly.quotient v lp1) in
        simplify (step sys0 v pc a1) sys'
    in
    List.map fst
      (iterate_until_stable elim (List.map (fun (_, c) -> (c, false)) (sort sys0)))

  let subst_constant is_int sys =
    let is_integer q = Q.(q =/ floor q) in
    let is_constant ((c, o), p) =
      match o with
      | Ge | Gt -> None
      | Eq -> (
        Vect.Bound.(
          match of_vect c with
          | None -> None
          | Some b ->
            if (not is_int) || is_integer (b.cst // b.coeff) then
              Monomial.get_var (LinPoly.MonT.retrieve b.var)
            else None) )
    in
    iterate_pivot is_constant sys

  (** {3 [subst] from the previous call}

      The clauses of a goal's CNF make [lia] problems that differ in one constraint (on the fast
      set, consecutive problems differ in one of about 60), and [pre_process] runs [subst] on each.
      [subst sys0] is stock's [iterate_pivot (is_substitution true) sys0] (above). When [sys0]
      differs from the system of the previous call in one inequality, it takes the rounds of that
      call and the results of the constraints they share, and computes only the new inequality's.
      Why that is stock's result:
      - Each round extracts the first constraint, in the order of [sort sys0] less the extracted
        ones, on which [p = is_substitution true] holds; [p] holds only on equalities, and a pivot
        keeps an inequality an inequality. Then it applies [step] (above: the function given to
        [simplify]) to each other constraint: a function of the constraint, of the round's
        variable [v], equation [pc] and quotient [a1], and of [sys0], which only [pivot_by]'s
        [get_sign sys0 a1] reads, and only when [a1] is not a constant.
      - [sort] is a stable sort on a key of each constraint alone, so the constraints that two
        systems share come in the same relative order; [align] pairs them in that order, equal by
        value ([equal]), and leaves at most one constraint of each system unpaired, which must be
        an inequality.
      - Values mean the same in both calls only if the monomial table maps each index to the same
        monomial: [MonT.same_snapshot] checks it. [p = is_substitution true] selects an equation
        only with [search_linear], that is [is_linear_for], so each round's quotient [a1] is a
        constant: [get_sign] answers from [construct_sign] without reading [sys0], and [pivot_by]
        multiplies the equation by the constraint's quotient and the constraint by [a1]. A step
        can register a monomial (a non-constant product, or [simplify_prf_rule] of a proof with a
        non-constant [MulC]); otherwise it reads only the indexes of its constraint and the
        equation, and its result is a function of their values. A record is kept only for a call
        that registered nothing ([subst_record]); so in a later call with the same table, the
        shared constraints' steps register nothing and give the recorded values. (Records are
        further kept only for linear systems, and the added inequality must be linear: a
        deliberate restriction to what the fast set needs, not one this argument uses.)
      - Then the equations, and so the rounds' [v], [pc] and [a1], are the same in both calls, the
        shared constraints take the same steps, and only the new inequality's steps are computed
        ([replay]). A round goes on when some step returns [Some]: [replay] checks that each
        round of the previous call goes on, or stops, for the same reason in this one (counting
        the steps without the replaced inequality's, plus the new one's), else it computes the
        call in full. The results come in the order of [sort sys0], less the extracted equations,
        as [simplify] and [extract] keep it (each reverses the list, so a round keeps its order).
      - The new inequality's steps are computed in the order of the rounds, as stock computes
        them, and are the only steps of the call that can register a monomial: a monomial it
        registers gets the index that stock gives it. If it registers one, the result is still
        stock's, but no record is kept for the next call; if [replay] then refuses, the full
        computation finds that monomial registered at the index it would give it, and computes
        stock's result again.
      A call [replay] does not answer is computed in full and recorded. *)
  type subst_record =
    { sr_mont : Monomial.t option array  (** [MonT.snapshot] at the call *)
    ; sr_input : t array  (** [sort sys0] *)
    ; sr_rounds : (var * t * Vect.t Lazy.t) array
          (** [v], [pc] and [a1] of each completed round, then of the round that stopped on
              [simplify], if one did *)
    ; sr_completed : int
    ; sr_some : int array  (** per round, the steps that returned [Some] *)
    ; sr_flags : int array  (** per constraint, bit [r] if its step in round [r] returned [Some] *)
    ; sr_final : (t * bool) option array
          (** per constraint, its value and flag after the completed rounds, [None] if extracted *)
    }

  let last_subst : subst_record option ref = ref None
  let subst_hits = ref 0
  let subst_cache_hits () = !subst_hits
  let subst_cache_clear () = last_subst := None

  let equal ((p1, o1), prf1) ((p2, o2), prf2) =
    o1 = o2 && Vect.equal p1 p2 && Int.equal (ProofFormat.OrdPrfRule.compare prf1 prf2) 0

  let linear c = try LinPoly.is_linear (polynomial c) with Not_found -> false

  (** [subst_record sys0 sorted]: [iterate_pivot (is_substitution true) sys0], where [sorted] is
      [sort sys0], each constraint carrying its position in [sorted]; and its record, if it is
      linear, registered nothing, and has at most 61 rounds *)
  let subst_record sys0 sorted =
    let p = is_substitution true in
    let input = Array.of_list (List.map snd sorted) in
    let n0 = Array.length input in
    let flags = Array.make n0 0 and rounds = ref [] and somes = ref [] in
    let completed = ref 0 in
    let mont = LinPoly.MonT.snapshot () in
    let elim sys =
      let oeq, sys' = extract (fun (_, (c, _)) -> p c) sys in
      match oeq with
      | None -> None
      | Some (v, (_, (pc, _))) ->
        let ((lp1, _), _) = pc in
        let a1 = lazy (LinPoly.quotient v lp1) in
        let r = !completed and some = ref 0 in
        let res =
          simplify
            (fun (id, c) ->
              match step sys0 v pc a1 c with
              | None -> None
              | Some c' ->
                incr some;
                if r < Sys.int_size - 1 then flags.(id) <- flags.(id) lor (1 lsl r);
                Some (id, c'))
            sys'
        in
        rounds := (v, pc, a1) :: !rounds;
        somes := !some :: !somes;
        if Option.has_some res then incr completed;
        res
    in
    let res = iterate_until_stable elim (List.mapi (fun id (_, c) -> (id, (c, false))) sorted) in
    let out = List.map (fun (_, (c, _)) -> c) res in
    (match mont with
     | Some mont
       when List.length !rounds < Sys.int_size - 1
            && LinPoly.MonT.same_snapshot mont
            && Array.for_all linear input ->
       let final = Array.make n0 None in
       List.iter (fun (id, c) -> final.(id) <- Some c) res;
       last_subst :=
         Some
           { sr_mont = mont
           ; sr_input = input
           ; sr_rounds = Array.of_list (List.rev !rounds)
           ; sr_completed = !completed
           ; sr_some = Array.of_list (List.rev !somes)
           ; sr_flags = flags
           ; sr_final = final }
     | _ -> last_subst := None);
    out

  (** [align old sorted]: [Some (m, gone, added)] where [m.(j)] is the position in [old] of the
      [j]th constraint of [sorted], or [-1] for the one constraint [added] that [old] does not
      have; [gone] is the one position of [old] that [sorted] does not have, or [-1]. The pairs
      are equal and in the same order in both. [None] if they differ in more. *)
  let align old sorted =
    let n = Array.length old in
    let s = Array.of_list (List.map snd sorted) in
    let m = Array.make (Array.length s) (-1) in
    let gone = ref (-1) and added = ref (-1) in
    let rec go i j =
      if i = n && j = Array.length s then true
      else if j < Array.length s && i < n && equal old.(i) s.(j) then (m.(j) <- i; go (i + 1) (j + 1))
      else if i < n && !gone < 0 && (j = Array.length s || (i + 1 < n && equal old.(i + 1) s.(j)))
      then (gone := i; go (i + 1) j)
      else if j < Array.length s && !added < 0 then (added := j; go i (j + 1))
      else if i < n && !gone < 0 then (gone := i; go (i + 1) j)
      else false
    in
    if go 0 0 then Some (m, !gone, !added) else None

  (** [replay r sys0 sorted]: [Some] of the result, from the record [r], when [sorted] differs from
      [r]'s input as above; [None] otherwise. Of the state that a later step reads, it changes only
      what the new inequality's steps register (see above); it forces the recorded [a1]s, which
      register nothing (each is a constant), and fills the table's caches. *)
  let replay r sys0 sorted =
    if not (LinPoly.MonT.same_snapshot r.sr_mont) then None
    else
      match align r.sr_input sorted with
      | None -> None
      | Some (m, gone, added) ->
        let ineq c = match snd (fst c) with Eq -> false | Ge | Gt -> true in
        let s = Array.of_list (List.map snd sorted) in
        if (gone >= 0 && not (ineq r.sr_input.(gone)))
           || (added >= 0 && not (ineq s.(added) && linear s.(added)))
        then None
        else
          let gone_flags = if gone >= 0 then r.sr_flags.(gone) else 0 in
          (* the steps of the added constraint [c] (if any), and whether each round goes on as
             before *)
          let nr = Array.length r.sr_rounds in
          let rec run k (c, flags) =
            if k = nr then Some (c, flags)
            else
              let v, pc, a1 = r.sr_rounds.(k) in
              let o = Option.bind c (step sys0 v pc a1) in
              let others = r.sr_some.(k) - ((gone_flags lsr k) land 1) in
              let goes_on = others > 0 || Option.has_some o in
              if k < r.sr_completed then
                if not goes_on then None
                else
                  match o with
                  | None -> run (k + 1) (c, flags)
                  | Some c' -> run (k + 1) (Some c', flags lor (1 lsl k))
              else if goes_on then None
              else Some (c, flags)
          in
          let start = if added >= 0 then Some (s.(added), false) else None in
          match run 0 (start, 0) with
          | None -> None
          | Some (c_added, flags_added) ->
            incr subst_hits;
            let n = Array.length s in
            let final = Array.init n (fun j -> if j = added then c_added else r.sr_final.(m.(j))) in
            last_subst :=
              if not (LinPoly.MonT.same_snapshot r.sr_mont) then None
              else
                Some
                  { r with
                    sr_input = s
                  ; sr_some =
                      Array.mapi
                        (fun k x -> x - ((gone_flags lsr k) land 1) + ((flags_added lsr k) land 1))
                        r.sr_some
                  ; sr_flags = Array.init n (fun j -> if j = added then flags_added else r.sr_flags.(m.(j)))
                  ; sr_final = final };
            Some (Array.fold_right (fun c acc -> match c with Some (c, _) -> c :: acc | None -> acc) final [])

  let subst sys0 =
    let sorted = sort sys0 in
    match Option.bind !last_subst (fun r -> replay r sys0 sorted) with
    | Some res -> res
    | None -> subst_record sys0 sorted

  let saturate_subst b sys0 =
    let select = is_substitution b in
    let gen (v, pc) ((c, op), prf) =
      if ISet.mem v (LinPoly.variables c) then
        linear_pivot sys0 pc v ((c, op), prf)
      else None
    in
    saturate select gen sys0

  (** [pivot_coeffs (q1, x) (v1, o1) (v2, o2)] is [Some (cv1, cv2)], the multipliers of
      [simple_pivot], or [None] where [simple_pivot] returns [None] *)
  let pivot_coeffs (q1, x) (_, o1) (v2, o2) =
    let q2 = Vect.get x v2 in
    if q2 =/ Q.zero then None
    else
      let cv1, cv2 =
        if Q.sign q1 <> Q.sign q2 then (Q.abs q2, Q.abs q1)
        else
          match (o1, o2) with
          | Eq, _ -> (q2, Q.abs q1)
          | _, Eq -> (Q.abs q2, q2)
          | _, _ -> (Q.zero, Q.zero)
      in
      if cv2 =/ Q.zero then None else Some (cv1, cv2)

  let pivot_proof cv1 prf1 cv2 prf2 =
    ProofFormat.add_proof (ProofFormat.mul_cst_proof cv1 prf1) (ProofFormat.mul_cst_proof cv2 prf2)

  let simple_pivot qx ((v1, o1), prf1) ((v2, o2), prf2) =
    match pivot_coeffs qx (v1, o1) (v2, o2) with
    | None -> None
    | Some (cv1, cv2) ->
      Some ((Vect.mul_add cv1 v1 cv2 v2, opAdd o1 o2), pivot_proof cv1 prf1 cv2 prf2)

  (** [simple_pivot_cut qx p q] is [Option.bind (simple_pivot qx p q) cutting_plane]. [cut]
      reads only the polynomial and the operator of the pivot, and its proof ([add_proof] of two
      [mul_cst_proof]s, built of constructors and [Vect.mul], which read and change no state and
      raise nothing) is built only when [cut] returns [Some]: the same values and exceptions. Most
      pivots of [fourier_small] have no cut, and their proofs were built for nothing. *)
  let simple_pivot_cut qx ((v1, o1), prf1) ((v2, o2), prf2) =
    match pivot_coeffs qx (v1, o1) (v2, o2) with
    | None -> None
    | Some (cv1, cv2) -> (
      match cut (Vect.mul_add cv1 v1 cv2 v2, opAdd o1 o2) with
      | None -> None
      | Some c -> Some (c, ProofFormat.CutPrf (pivot_proof cv1 prf1 cv2 prf2)) )

end

module BoundWithProof =
struct

type t = Vect.Bound.t * op * ProofFormat.prf_rule

let make ((p, o), prf) = match Vect.Bound.of_vect p with
| None -> None
| Some b -> Some (b, o, prf)

let padd (o1, prf1) (o2, prf2) = (opAdd o1 o2, ProofFormat.add_proof prf1 prf2)

let pmul (o1, prf1) (o2, prf2) = (opMult o1 o2, ProofFormat.mul_proof prf1 prf2)

let plet (o1,p1) (o2,p2) f  =
    match ProofFormat.pr_unit p1 , ProofFormat.pr_unit p2 with
    | true , true -> f (o1,p1) (o2,p2)
    | false , false ->
      let (o,prf) = f (o1,ProofFormat.Ref 1) (o2,ProofFormat.Ref 0) in
      (o, ProofFormat.LetPrf(p1,ProofFormat.LetPrf(p2,prf)))
    | true , false ->
      let (o,prf) = f (o1,p1) (o2,ProofFormat.Ref 0) in
      (o, ProofFormat.LetPrf(p2,prf))
    | false , true ->
      let (o,prf) = f (o1,ProofFormat.Ref 0) (o2,p2) in
      (o,ProofFormat.LetPrf(p1,prf))

let pext c (o, prf) =
  if c =/ Q.zero then (Eq, ProofFormat.Zero)
  else (o, ProofFormat.mul_cst_proof c prf)

let mul_bound (b1, o1, prf1) (b2, o2, prf2) =
  let open Vect.Bound in
  match (b1, b2) with
  | {cst = c1; var = v1; coeff = c1'},
    {cst = c2; var = v2; coeff = c2'} ->
    let good_coeff b o =
      match o with
      | Eq -> Some (Q.neg b)
      | _ -> if b <=/ Q.zero then Some (Q.neg b) else None
    in
    match (good_coeff c1 o2, good_coeff c2 o1) with
    | None, _ | _, None -> None
    | Some c1, Some c2 ->
      let w1 = (o1, prf1) in
      let w2 = (o2, prf2) in
      let (o, prf) = plet w1 w2 (fun w1 w2 -> padd (padd (pmul w1 w2) (pext c1 w2)) (pext c2 w1)) in
      let b = {
        cst = Q.neg (c1 */ c2);
        var = LinPoly.MonT.register (Monomial.prod (LinPoly.MonT.retrieve v1) (LinPoly.MonT.retrieve v2));
        coeff = c1' */ c2';
      } in
      Some (b, o, prf)

let bound (b, _, _) = b

let proof (b, o, w) =
  let p = Vect.Bound.to_vect b in
  ((p, o), w)
end

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
