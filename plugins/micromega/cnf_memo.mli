(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The CNF conversion of micromega ([rxcnf], [xcnf], [tauto_checker]) with its pair checks
    computed once per pair of literals. For [unsat], [deduce], [normalise] and [negate] of one
    domain, and [M = Make (struct type t = ... let incompatible f f' = match deduce f f' with
    Some u -> unsat u | None -> false end)], with [st = M.create ()],
    [rxcnf M.unsat (M.deduce st) (fun x a -> M.tag st (normalise x a))
       (fun x a -> M.tag st (negate x a)) pol k f]
    is [rxcnf unsat deduce normalise negate pol k f] once [M.strip_cnf] is applied to its CNF, and
    the same holds of [xcnf] and of [tauto_checker] with a checker that applies [M.strip] to the
    literals of its clause. The implementation says why. *)

module type Literal = sig
  type t
  (** A literal: a normalised constraint ([nFormula]). Structural equality and hash must be
      meaningful on it: no functions, no cycles. *)

  val incompatible : t -> t -> bool
  (** [incompatible t t'] is [match deduce t t' with Some u -> unsat u | None -> false]. *)
end

module Make (L : Literal) : sig
  type lit
  (** A literal with an identifier, the same for structurally equal literals. *)

  type t
  (** The literals of one conversion and the pair checks computed so far. *)

  val create : unit -> t

  val tag : t -> (L.t * 'a) list list -> (lit * 'a) list list

  val strip : lit -> L.t

  val strip_cnf : (lit * 'a) list list -> (L.t * 'a) list list

  val unsat : lit -> bool

  val deduce : t -> lit -> lit -> lit option

  val bytes : t -> int
  (** For the tests: the bytes of the memo's rows, at most [1 lsl 20 + 64 * stored t]. *)

  val stored : t -> int
  (** For the tests: the pair checks stored, at most the checks the conversion made. *)
end
