(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The CNF conversion of lia, nia and lra ([Tauto.rxcnf] and [Tauto.xcnf], extracted in
   [Micromega] and [Zchecker]) puts a literal [t] into a clause by checking [t] against each
   literal [t'] already there and against itself ([radd_term], [add_term]): when
   [deduce t t'] is [Some u] and [unsat u], the two literals together are unsatisfiable and the
   clause is dropped. Distributing a disjunction over a conjunction meets the same pairs of
   literals in many clauses, and every meeting computes [deduce] again (a polynomial sum). On the
   files of speed lane R2's fast set these checks were 11-16% of the samples of the CNF at tactic
   time and nearly all of the extracted checker's (dispatch://INFRA-217).

   Here the conversion runs on literals that carry an identifier, the same for structurally equal
   literals, and the check of a pair of identifiers is computed once.

   Why the result is the conversion's on plain literals: [rxcnf], [xcnf] and [tauto_checker] are
   polymorphic in the type of literals and use no polymorphic comparison or hash, so they reach a
   literal only through the four functions they are given. They get literals only from
   [normalise] and [negate]; and they use [deduce] and [unsat] only as above, where
   [Some u] with [not (unsat u)] takes the branch of [None], and [u] is not kept
   ([Micromega.radd_term], [Zchecker.add_term]). [tag] wraps the literals of [normalise] and
   [negate] and changes nothing else; [deduce] gives [Some Incompatible] exactly when [deduce]
   gives [Some u] with [unsat u] on the plain literals, a pure function of the two literals,
   which are structurally those of the identifiers; [unsat] recognises [Incompatible]. So the
   clauses, with [strip] applied to their literals, and the trace are those of the conversion on
   plain literals. Physical sharing between clauses can differ; nothing downstream depends on it. *)

module type Literal = sig
  type t

  val incompatible : t -> t -> bool
  (** [incompatible t t'] is [match deduce t t' with Some u -> unsat u | None -> false]. *)
end

module Make (L : Literal) = struct
  type lit = Lit of int * L.t | Incompatible

  (* Structural hash and equality: literals hold no functions and no cycles. The hash reads more
     of a literal than [Hashtbl.hash], whose first ten words are often those of many polynomials. *)
  module Ids = Hashtbl.Make (struct
    type t = L.t

    let equal = ( = )
    let hash f = Hashtbl.hash_param 64 256 f
  end)

  (* [rows.(i)] holds the checks of the pairs [(i, j)] computed so far, one byte per [j]: '\000'
     not computed, '\001' compatible, '\002' incompatible. The identifiers are dense, so a lookup
     is two loads. A row can be longer than the number of checks it holds, so the bytes of all
     rows are kept within [budget] (see [store]); [bytes] counts them and [stored] counts the
     checks stored. *)
  type t = {
    ids : int Ids.t;
    mutable rows : Bytes.t array;
    mutable bytes : int;
    mutable stored : int;
  }

  (* One table per conversion: the identifiers are those of its literals. *)
  let create () = {ids = Ids.create 16; rows = [||]; bytes = 0; stored = 0}

  (* The identifier of [f], the same for structurally equal literals. *)
  let lit st f =
    match Ids.find_opt st.ids f with
    | Some i -> Lit (i, f)
    | None ->
      let i = Ids.length st.ids in
      Ids.add st.ids f i;
      Lit (i, f)

  let tag st cnf = CList.map (CList.map (fun (f, a) -> (lit st f, a))) cnf

  (* [Incompatible] is only ever the [u] of [deduce], which the conversions do not keep, so it is
     never in a clause. *)
  let strip = function Lit (_, f) -> f | Incompatible -> assert false

  (* [CList.map] runs in constant stack: a CNF can have many clauses. *)
  let strip_cnf cnf = CList.map (CList.map (fun (l, a) -> (strip l, a))) cnf

  let unsat = function Incompatible -> true | Lit _ -> false

  let lookup st i j =
    if i < Array.length st.rows then
      let row = Array.unsafe_get st.rows i in
      if j < Bytes.length row then Bytes.unsafe_get row j else '\000'
    else '\000'

  (* The bytes the rows may hold: 1 MB, plus 64 bytes per check stored. A check that does not fit
     is not stored, and is computed again when the conversion meets the pair again, as without the
     memo. So the memo's memory is bounded by the number of checks the conversion makes, which is
     its work without the memo, whatever the shape of the formula (a conjunction of many
     disjunctions of distinct atoms makes many literals and few checks per literal), plus the
     array of rows and the table of identifiers, a few words per literal. *)
  let budget st = (1 lsl 20) + 64 * st.stored

  let bytes st = st.bytes

  let stored st = st.stored

  (* The array and a row grow to hold every identifier made so far, and at least double, so
     each grows a logarithmic number of times. *)
  let store st i j c =
    let n = Ids.length st.ids in
    let len = Array.length st.rows in
    if i >= len then begin
      let rows = Array.make (max (max n (i + 1)) (2 * len)) Bytes.empty in
      Array.blit st.rows 0 rows 0 len;
      st.rows <- rows
    end;
    let row = st.rows.(i) in
    let len = Bytes.length row in
    if j < len then begin
      Bytes.set row j c;
      st.stored <- st.stored + 1
    end
    else begin
      let size = max (max n (j + 1)) (2 * len) in
      if st.bytes + size - len <= budget st then begin
        let r = Bytes.make size '\000' in
        Bytes.blit row 0 r 0 len;
        st.rows.(i) <- r;
        st.bytes <- st.bytes + size - len;
        Bytes.set r j c;
        st.stored <- st.stored + 1
      end
    end

  let deduce st l l' =
    match (l, l') with
    | Lit (i, f), Lit (j, f') ->
      let b =
        match lookup st i j with
        | '\001' -> false
        | '\002' -> true
        | _ ->
          let b = L.incompatible f f' in
          store st i j (if b then '\002' else '\001');
          b
      in
      if b then Some Incompatible else None
    | Incompatible, _ | _, Incompatible -> assert false
end
