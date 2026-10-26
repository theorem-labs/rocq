(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [checker ist t] is the tactic value [t] (the checker argument of xlia or
    xnia) as a tactic. When [t] is Stdlib's [Lia.zchecker] and the extracted
    [ZTautoChecker] accepts the certificate, it builds [zchecker]'s proof term
    without running the VM on its cast; otherwise it is
    [Tacinterp.tactic_of_value ist t]. See zcheck_oracle.ml. *)
val checker : Ltac_plugin.Tacinterp.interp_sign -> Geninterp.Val.t -> unit Proofview.tactic
