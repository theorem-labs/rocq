(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open NumCompat

module ISet : sig
  include CSet.S with type elt = int

  val pp : out_channel -> t -> unit
end

module IMap : sig
  include CMap.ExtS with type key = int and module Set := ISet

  (** [from k  m] returns the submap of [m] with keys greater or equal k *)
  val from : key -> 'elt t -> 'elt t
end

module Cmp : sig
  val compare_list : ('a -> 'b -> int) -> 'a list -> 'b list -> int
  val compare_lexical : (unit -> int) list -> int
end

module Tag : sig
  type t

  val pp : out_channel -> t -> unit
  val next : t -> t
  val max : t -> t -> t
  val from : int -> t
  val to_int : t -> int
  val compare : t -> t -> int
end

module TagSet : CSig.SetS with type elt = Tag.t

module McPrinter : sig
  module Mc = Micromega
  val pp_nat : out_channel -> Mc.nat -> unit
  val pp_positive : out_channel -> Mc.positive -> unit
  val pp_z : out_channel -> Mc.z -> unit
  val pp_pol : (out_channel -> 'a -> unit) -> out_channel -> 'a Mc.pol -> unit
  val pp_psatz : (out_channel -> 'a -> unit) -> out_channel -> 'a Mc.psatz -> unit
  val pp_proof_term : out_channel -> Mc.zArithProof -> unit
end
val pp_list :
  string -> (out_channel -> 'a -> unit) -> out_channel -> 'a list -> unit

module CamlToCoq : sig
  val positive : int -> Micromega.positive
  val bigint : Z.t -> Micromega.z
  val n : int -> Micromega.n
  val nat : int -> Micromega.nat
  val q : Q.t -> Micromega.q
  val index : int -> Micromega.positive
  val z : int -> Micromega.z
  val positive_big_int : Z.t -> Micromega.positive
end

module CoqToCaml : sig
  val z_big_int : Micromega.z -> Z.t
  val z : Micromega.z -> int
  val q_to_num : Micromega.q -> Q.t
  val positive : Micromega.positive -> int
  val n : Micromega.n -> int
  val nat : Micromega.nat -> int
  val index : Micromega.positive -> int
end

module Hash : sig
  val eq_op1 : Micromega.op1 -> Micromega.op1 -> bool
  val eq_op2 : Micromega.op2 -> Micromega.op2 -> bool
  val eq_positive : Micromega.positive -> Micromega.positive -> bool
  val eq_z : Micromega.z -> Micromega.z -> bool
  val eq_q : Micromega.q -> Micromega.q -> bool

  val eq_pol :
    ('a -> 'a -> bool) -> 'a Micromega.pol -> 'a Micromega.pol -> bool

  val eq_pair :
    ('a -> 'a -> bool) -> ('b -> 'b -> bool) -> 'a * 'b -> 'a * 'b -> bool

  val hash_op1 : int -> Micromega.op1 -> int
  val hash_pol : (int -> 'a -> int) -> int -> 'a Micromega.pol -> int

  val hash_pair :
    (int -> 'a -> int) -> (int -> 'b -> int) -> int -> 'a * 'b -> int

  val hash_z : int -> Micromega.z -> int
  val hash_q : int -> Micromega.q -> int
  val hash_string : int -> string -> int
  val hash_elt : ('a -> int) -> int -> 'a -> int
end

val all_pairs : ('a -> 'a -> 'b) -> 'a list -> 'b list
val is_sublist : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val extract : ('a -> 'b option) -> 'a list -> ('b * 'a) option * 'a list
val extract_all : ('a -> 'b option) -> 'a list -> 'b list * 'a list

val iterate_until_stable : ('a -> 'a option) -> 'a -> 'a
val simplify : ('a -> 'a option) -> 'a list -> 'a list option

val saturate :
  ('a -> 'b option) -> ('b * 'a -> 'a -> 'a option) -> 'a list -> 'a list

val app_funs : ('a -> 'b option) list -> 'a -> 'b option
val command : string -> string array -> 'a -> 'b

(** The work counter of lia and nia: the one quantity that the budgets of their early-failure
    check and certificate reuse ([Coq_micromega.witness_list], [ModelSearch.find_model]) read in
    the tactics, where speed-7.5 read [Sys.time].

    Its inputs, all of them: [tick] is called at these nine places and nowhere else (each place
    says so in a comment or docstring, and [grep -n "Work\.tick"] in this directory lists exactly
    them).
    - [Simplex.pivot_with]: each row a pivot rewrites.
    - [Certificate.dev_form]: each node of an expression the development of a constraint walks.
    - [ModelSearch.model_eval]: each node of a constraint the model search evaluates at a point.
    - [Coq_micromega.int_early]: each lookup of the persistent cache.
    - [Coq_micromega.witness_list]: each atom the check sizes ([size]); each formula reuse hashes
      ([positions]), reads for a certificate ([cited]) or renumbers ([renumber]); each try.
    Each is a step of a computation on the call's clauses and on state the process's earlier
    calls left, so the count is a function of the commands run, in their order; nothing outside
    the plugin moves it. Nothing in it reads a clock.

    That is the whole argument that the budgets are independent of the clock. It does not rest on
    the order of the provers' memo hits: that order exists (the development memo is shared by
    every call of a process, and the check's model searches go through it too), and the count
    depends on it (a hit adds no [tick] in [dev_form]), but the order is itself fixed by the
    commands and by earlier budget decisions, which are functions of this count. *)
module Work : sig
  (** adds a unit of work *)
  val tick : unit -> unit

  (** [now ()]: the units counted so far in this process, as a float, the type of the budgets *)
  val now : unit -> float
end
