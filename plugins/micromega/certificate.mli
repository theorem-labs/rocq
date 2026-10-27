(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Mc = Micromega

type ('prf, 'model) res = Prf of 'prf | Model of 'model | Unknown
type zres = (Mc.zArithProof, int * Mc.z list) res
type qres = (Mc.q Mc.psatz, int * Mc.q list) res

(** [q_cert_of_pos prf] converts a Sos proof into a rational Rocq proof *)
val q_cert_of_pos : Sos_types.positivstellensatz -> Mc.q Mc.psatz

(** [z_cert_of_pos prf] converts a Sos proof into an integer Rocq proof *)
val z_cert_of_pos : Sos_types.positivstellensatz -> Mc.z Mc.psatz

(** [lia depth sys] generates an unsat proof for the linear constraints in [sys].
    It answers a problem it solved before in this process from a memo: the result, profile and
    state of a new search (see certificate.ml, "Memo of the searches"). *)
val lia : int -> (Mc.z Mc.pExpr * Mc.op1) list -> zres

(** [nlia depth sys] generates an unsat proof for the non-linear constraints in [sys].
    The solver is incomplete -- the problem is undecidable. It answers from the memo as [lia]. *)
val nlia : int -> (Mc.z Mc.pExpr * Mc.op1) list -> zres

(** The number of calls of [lia] and [nlia] answered by the memo, the number of problems it holds,
    and the most it holds before it starts again empty (for tests). *)
val memo_hits : unit -> int
val memo_size : unit -> int
val memo_capacity : int

(** [linear_prover_with_cert depth sys] generates an unsat proof for the linear constraints in [sys].
    Over the rationals, the solver is complete. *)
val linear_prover_with_cert : int -> (Mc.q Mc.pExpr * Mc.op1) list -> qres

(** [nlinear depth sys] generates an unsat proof for the non-linear constraints in [sys].
    The solver is incompete -- the problem is decidable. *)
val nlinear_prover : int -> (Mc.q Mc.pExpr * Mc.op1) list -> qres

(** [develop_z_constraints depth sys] is [sys] as [lia] and [nia] develop it before their search:
    linear constraints whose atoms are the monomials of [sys]. Like their entry points, it clears the
    monomial table [Polynomial.LinPoly.MonT] and sets the depth bound. *)
val develop_z_constraints :
  int -> (Mc.z Mc.pExpr * Mc.op1) list -> Polynomial.WithProof.t list
