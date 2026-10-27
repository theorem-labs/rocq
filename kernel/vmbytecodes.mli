(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* $Id$ *)

open Names
open Vmvalues
open Constr

module Label :
  sig
    type t = int
    val no : t
    val create : unit -> t
    val reset_label_counter : unit -> unit
  end

type caml_prim =
| CAML_Arraymake
| CAML_Arrayget
| CAML_Arraydefault
| CAML_Arrayset
| CAML_Arraycopy
| CAML_Arraylength
| CAML_Stringmake
| CAML_Stringlength
| CAML_Stringget
| CAML_Stringsub
| CAML_Stringcat
| CAML_Stringcompare

(** Operations of the standard library's binary numbers that the machine
    evaluates natively instead of interpreting them one digit at a time. See
    [Vmznative], which decides which constants carry them. *)
type znative_op =
| ZNadd      (** [Z.add] of two closed [Z] below the native window *)
| ZNpossub   (** [Z.pos_sub] of two closed [positive] below the window *)
| ZNposadd   (** [Pos.add] of two closed [positive] below the window *)

type instruction =
  | Klabel of Label.t
  | Kacc of int                         (** accu = sp[n] *)
  | Kenvacc of int                      (** accu = rocq_env[n] *)
  | Koffsetclosure of int               (** accu = &rocq_env[n] *)
  | Kpush                               (** sp = accu :: sp *)
  | Kpop of int                         (** sp = skipn n sp *)
  | Kpush_retaddr of Label.t            (** sp = pc :: rocq_env :: rocq_extra_args :: sp ; rocq_extra_args = 0 *)
  | Kshort_apply of int                 (** number of arguments (arguments on top of stack) *)
  | Kapply of int                       (** number of arguments (arguments on top of stack) *)
  | Kappterm of int * int               (** number of arguments, slot size *)
  | Kreturn of int                      (** slot size *)
  | Kjump
  | Krestart
  | Kgrab of int                        (** number of arguments *)
  | Kgrabrec of int                     (** rec arg *)
  | Kclosure of Label.t * int           (** label, number of free variables *)
  | Kclosurerec of int * int * Label.t array * Label.t array
                   (** nb fv, init, lbl types, lbl bodies *)
  | Kclosurecofix of int * int * Label.t array * Label.t array
                   (** nb fv, init, lbl types, lbl bodies *)
  | Kgetglobal of Constant.t
  | Ksubstinstance of UVars.Instance.t
  | Kconst of structured_constant
  | Kmakeblock of (* size: *) int * tag (** allocate an ocaml block. Index 0
                                         ** is accu, all others are popped from
                                         ** the top of the stack  *)
  | Kmakeswitchblock of Label.t * Label.t * annot_switch * int
  | Kswitch of Label.t array * Label.t array (** consts,blocks *)
  | Kpushfields of int
  | Kfield of int                       (** accu = accu[n] *)
  | Ksetfield of int                    (** accu[n] = sp[0] ; sp = pop sp *)
  | Kstop
  | Ksequence of bytecodes
  | Kproj of int
  | Kensurestackcapacity of int
  | Kbinnum of int * int                (** routine, number of arguments: run the
                                           C routine of {!Vmbinnum} on the
                                           arguments sp[0..n-1]; if it accepts
                                           them, return its result as
                                           [Kreturn n] does *)
  | Kbinnumcall of int * int * Label.t  (** routine, number of arguments,
                                           label: at a call site, run the C
                                           routine on sp[0..n-1]; if it
                                           accepts them, set accu to its
                                           result, pop the n arguments and
                                           jump to the label *)

  | Kbranch of Label.t                  (** jump to label, is it needed ? *)
  | Kprim of CPrimitives.t * pconstant
  | Kcamlprim of caml_prim * Label.t
  | Kznative of znative_op
      (** native binary-number operation, at the entry of the function whose
          definition carries it, where its two arguments are sp[0] and sp[1];
          it returns the result, or falls through to the body when an argument
          is not a closed number *)

and bytecodes = instruction list

val pp_bytecodes : bytecodes -> Pp.t

type fv_elem =
  FVnamed of Id.t
| FVrel of int

type fv = fv_elem array

val pp_fv_elem : fv_elem -> Pp.t

val caml_prim_to_prim : caml_prim -> CPrimitives.t
