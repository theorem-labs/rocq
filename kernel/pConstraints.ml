(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open Sorts

type t = ElimConstraints.t * Quality.Set.t * UnivConstraints.t

type pconstraints = t

let make q u = (q, Quality.Set.empty, u)

let qualities (q, _, _) = q

let above_prop (_, above, _) = above

let univs (_, _, u) = u

let add_quality q (qc, above, lc) = (ElimConstraints.add q qc, above, lc)

let add_above_prop q (qc, above, lc) = (qc, Quality.Set.add q above, lc)

let add_univ u (qc, above, lc) = (qc, above, UnivConstraints.add u lc)

let check_above_prop_quality ~is_above_prop = function
  | Quality.QConstant QProp | Quality.QConstant QType -> true
  | Quality.QVar q -> is_above_prop q
  | Quality.QConstant QSProp | Quality.QGlobal _ -> false

let of_qualities qc = make qc UnivConstraints.empty

let of_above_prop above = (ElimConstraints.empty, above, UnivConstraints.empty)

let of_univs lc = make ElimConstraints.empty lc

let set_qualities qc (_,above,lc) = (qc, above, lc)

let set_above_prop above (qc,_,lc) = (qc, above, lc)

let set_univs lc (qc,above,_) = (qc, above, lc)

let empty = (ElimConstraints.empty, Quality.Set.empty, UnivConstraints.empty)

let is_empty (qc, above, lc) =
  ElimConstraints.is_empty qc && Quality.Set.is_empty above && UnivConstraints.is_empty lc

let equal (qc, above, lc) (qc', above', lc') =
  ElimConstraints.equal qc qc' && Quality.Set.equal above above' && UnivConstraints.equal lc lc'

let union (qc, above, lc) (qc', above', lc') =
  (ElimConstraints.union qc qc', Quality.Set.union above above', UnivConstraints.union lc lc')

let fold (qf, lf) (qc, _, lc) (x, y) =
  (ElimConstraints.fold qf qc x, UnivConstraints.fold lf lc y)

let diff (qc, above, lc) (qc', above', lc') =
  (ElimConstraints.diff qc qc', Quality.Set.diff above above', UnivConstraints.diff lc lc')

let elements (qc, above, lc) =
  (ElimConstraints.elements qc, Quality.Set.elements above, UnivConstraints.elements lc)

let filter_qualities f (qc, above, lc) =
  (ElimConstraints.filter f qc, above, lc)

let filter_univs f (qc, above, lc) =
  (qc, above, UnivConstraints.filter f lc)

let pr (printer:Sorts.printer) (qc, above, lc) =
  let open Pp in
  let pieces =
    (if ElimConstraints.is_empty qc then [] else [ElimConstraints.pr printer.prq qc])
    @ (if Quality.Set.is_empty above then [] else
        [prlist_with_sep spc
           (fun q -> str "Prop <= " ++ Quality.pr printer.prq q)
           (Quality.Set.elements above)])
    @ (if UnivConstraints.is_empty lc then [] else [UnivConstraints.pr printer.pru lc])
  in
  v 0 (prlist_with_sep pr_comma (fun x -> x) pieces)

module HPConstraints =
  Hashcons.Make(
    struct
      type t = pconstraints
      let hash_qualities qualities =
        Quality.Set.fold
          (fun q h -> Hashset.Combine.combine h (Quality.hash q))
          qualities 0

      let hashcons (qf, above, uf) =
        let hqf, qf = ElimConstraints.hcons qf in
        let huf, uf = UnivConstraints.hcons uf in
        Hashset.Combine.(combine3 hqf (hash_qualities above) huf), (qf, above, uf)
      let eq (qc, above, uc) (qc', above', uc') =
        qc == qc' && Quality.Set.equal above above' && uc == uc'
    end)

let hcons =
  Hashcons.simple_hcons
    HPConstraints.generate
    HPConstraints.hcons ()

(** A value with universe constraints. *)
type 'a constrained = 'a * t

let constraints_of (_, cst) = cst

(** Constraints functions. *)

type 'a constraint_function = 'a -> 'a -> t -> t

let enforce_eq_univ u v c =
  (* We discard trivial constraints like u=u *)
  if Level.equal u v then c
  else add_univ (u, UnivConstraint.Eq, v) c

let enforce_leq_univ u v c =
  if Level.equal u v then c
  else add_univ (u, UnivConstraint.Le, v) c

let enforce_elim_to q1 q2 csts =
  if QGraph.ElimTable.eliminates_to q1 q2 then csts
  else add_quality (q1, ElimConstraint.ElimTo, q2) csts
