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

type pos_function =
  | Pos_compare_cont
  | Pos_eqb
  | Pos_add
  | Pos_succ
  | Pos_mul

val pos_function_to_string : pos_function -> string

type retroknowledge = {
    retro_int63 : Constant.t option;
    retro_float64 : Constant.t option;
    retro_string : Constant.t option;
    retro_array : Constant.t option;
    retro_pos : (constructor * constructor * constructor) option; (* xI, xO, xH *)
    retro_bool : (constructor * constructor) option; (* true, false *)
    retro_carry : (constructor * constructor) option; (* C0, C1 *)
    retro_pair : constructor option;
    retro_cmp : (constructor * constructor * constructor) option;
                    (* Eq, Lt, Gt *)
    retro_f_cmp : (constructor * constructor * constructor * constructor)
                  option;
                    (* FEq, FLt, FGt, FNotComparable *)
    retro_f_class : (constructor * constructor * constructor * constructor
                     * constructor * constructor * constructor * constructor
                     * constructor)
                      option;
                    (* PNormal, NNormal, PSubn, NSubn,
                       PZero, NZero, PInf, NInf,
                       NaN *)
    retro_pos_functions : (pos_function * Constant.t) list;
}

val empty : retroknowledge

type action =
  | Register_ind : 'a CPrimitives.prim_ind * inductive -> action
  | Register_type : 'a CPrimitives.prim_type * Constant.t -> action
  | Register_pos_function : pos_function * Constant.t -> action
