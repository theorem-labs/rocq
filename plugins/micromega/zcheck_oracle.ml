(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* lia and nia end with Stdlib's [Lia.zchecker] (its text is at [zchecker_parts]):
   [intros __wit __varmap __ff], then
     [exact (ZTautoChecker_sound __ff __wit
               (@eq_refl bool true <: @eq bool (ZTautoChecker __ff __wit) true) ...)].
   Pretyping checks the cast with the bytecode VM (the VM evaluates
   [ZTautoChecker] on the bodies of [__ff] and [__wit]), and the kernel checks it
   again at Qed.

   [checker] is the tactic that xlia and xnia run in place of [zchecker]. When the
   tactic is Stdlib's own [zchecker] ([zchecker_parts]) and the declaration of
   [ZTautoChecker] that its cast names has the fingerprint of the definitions
   that [Zchecker] was extracted from ([fingerprint], no opaque constant;
   [state_for]), it reads the formula and the certificate into values of
   [Zchecker] and evaluates [Zchecker.zTautoChecker] on them. If the result is
   [true], it runs [zchecker]'s [intros], then pretypes the glob term of
   [zchecker]'s [exact] (taken from [zchecker]'s body) without the VM conversion
   of its cast, and gives the term with [exact_no_check]. In all other cases (the
   result is [false], a term is not made of the expected constructors, an
   exception, the pretyping fails, Ltac debugging or profiling on) it runs
   [zchecker] itself. The kernel still runs the VM on the cast at Qed.

   [Set Debug "zcheck"] (after [Require Lia], which loads this plugin and so
   declares the flag) prints the digest of [zchecker]'s body and the
   fingerprint of [ZTautoChecker] each time they are computed (zchecker.ml says
   how to regenerate the extraction and the two expected digests). *)

open Names
open Constr
open Declarations

module Zc = Zchecker

exception Reject

let debug = CDebug.create ~name:"zcheck" ()

(** {1 Fingerprint of the definitions that ZTautoChecker reaches} *)

(* [fingerprint env c] serializes the type and the body of [c] and of every
   constant that they reach, and the declarations of every inductive type that
   they reach (constructor types included), in the order in which the traversal
   meets them. Binder names are left out. It returns the MD5 digest of the
   serialization, the number of opaque constants and the inductive blocks. *)
let fingerprint env checker =
  let buf = Buffer.create 65536 in
  let add = Buffer.add_string buf in
  let addi i = add (string_of_int i); Buffer.add_char buf ' ' in
  let seen = Hashtbl.create 257 in
  let queue = Queue.create () in
  let opaque = ref 0 in
  let minds = ref [] in
  let visit key item =
    if not (Hashtbl.mem seen key) then begin
      Hashtbl.add seen key ();
      Queue.push item queue
    end
  in
  let const c =
    let k = KerName.to_string (Constant.canonical c) in
    add "C"; add k; add " "; visit k (`Const c)
  in
  let ind (m, i) =
    let k = KerName.to_string (MutInd.canonical m) in
    add "I"; add k; add " "; addi i; visit k (`Mind m)
  in
  let inst u =
    add (Pp.string_of_ppcmds (UVars.Instance.pr Sorts.QVar.raw_pr Univ.Level.raw_pr u));
    add " "
  in
  let rel = function
    | Sorts.Relevant -> add "r"
    | Sorts.Irrelevant -> add "i"
    | Sorts.RelevanceVar _ -> add "v"
  in
  let rec term c =
    match kind c with
    | Rel n -> add "R"; addi n
    | Var id -> add "V"; add (Id.to_string id); add " "
    | Meta n -> add "M"; addi n
    | Evar _ -> add "E "
    | Sort s -> add "S"; add (Pp.string_of_ppcmds (Sorts.debug_print s)); add " "
    | Cast (c, k, t) ->
      add (match k with VMcast -> "Kv" | NATIVEcast -> "Kn" | DEFAULTcast -> "Kd");
      term c; term t
    | Prod (na, t, c) -> add "P"; rel na.Context.binder_relevance; term t; term c
    | Lambda (na, t, c) -> add "L"; rel na.Context.binder_relevance; term t; term c
    | LetIn (na, b, t, c) ->
      add "D"; rel na.Context.binder_relevance; term b; term t; term c
    | App (f, args) -> add "A"; addi (Array.length args); term f; Array.iter term args
    | Const (c, u) -> const c; inst u
    | Ind (i, u) -> ind i; inst u
    | Construct ((i, j), u) -> add "N"; addi j; ind i; inst u
    | Case (ci, u, params, ((nas, p), r), iv, c, brs) ->
      add "W"; ind ci.ci_ind; inst u;
      addi (Array.length params); Array.iter term params;
      addi (Array.length nas); term p; rel r;
      (match iv with
       | NoInvert -> add "n"
       | CaseInvert {indices} -> add "i"; addi (Array.length indices); Array.iter term indices);
      term c;
      addi (Array.length brs);
      Array.iter (fun (nas, b) -> addi (Array.length nas); term b) brs
    | Fix ((ri, i), (_, tys, bds)) ->
      add "F"; addi (Array.length bds); Array.iter addi ri; addi i;
      Array.iter term tys; Array.iter term bds
    | CoFix (i, (_, tys, bds)) ->
      add "G"; addi (Array.length bds); addi i; Array.iter term tys; Array.iter term bds
    | Proj (p, r, c) ->
      let pr = Projection.repr p in
      add "J"; ind (Projection.Repr.inductive pr); addi (Projection.Repr.arg pr);
      add (if Projection.unfolded p then "u" else "f"); rel r; term c
    | Int i -> add "Z"; add (Uint63.to_string i); add " "
    | Float f -> add "Q"; add (Float64.to_hex_string f); add " "
    | String s ->
      let s = Pstring.to_string s in
      add "T"; addi (String.length s); add s
    | Array (u, vs, d, t) ->
      add "Y"; inst u; addi (Array.length vs); Array.iter term vs; term d; term t
  in
  const checker;
  while not (Queue.is_empty queue) do
    match Queue.pop queue with
    | `Const c ->
      let cb = Environ.lookup_constant c env in
      add "\nconstant "; add (KerName.to_string (Constant.canonical c)); add "\n";
      term cb.const_type; add "\n";
      (match cb.const_body with
       | Def b -> add "def "; term b
       | OpaqueDef _ -> incr opaque; add "opaque"
       | Undef _ -> add "undef"
       | Primitive p -> add "primitive "; add (CPrimitives.to_string p)
       | Symbol _ -> add "symbol")
    | `Mind m ->
      let mib = Environ.lookup_mind m env in
      minds := m :: !minds;
      add "\ninductive "; add (KerName.to_string (MutInd.canonical m)); add "\n";
      add (match mib.mind_finite with Finite -> "F" | CoFinite -> "C" | BiFinite -> "B");
      addi mib.mind_nparams;
      Array.iter (fun mip ->
          add "\n "; add (Id.to_string mip.mind_typename); add " ";
          add (match mip.mind_record with NotRecord -> "n" | FakeRecord -> "f" | PrimRecord _ -> "p");
          term mip.mind_user_arity;
          Array.iteri (fun j id ->
              add "\n  "; add (Id.to_string id); add " "; term mip.mind_user_lc.(j))
            mip.mind_consnames)
        mib.mind_packets
  done;
  (Digest.to_hex (Digest.string (Buffer.contents buf)), !opaque, !minds)

(* The fingerprint of Stdlib 9.2.0's ZTautoChecker, from which [Zchecker] was
   extracted. *)
let expected_fingerprint = "07cfb5d54d855fd6c8ce7f3e7d93dacd"

(** {1 Reading terms into values of Zchecker} *)

type ind = { ind : inductive; np : int }

type state =
  { pos : ind
  ; z : ind
  ; n : ind
  ; nat : ind
  ; list : ind
  ; option : ind
  ; unit : ind
  ; kind : ind
  ; gform : ind
  ; form : ind
  ; pexpr : ind
  ; op2 : ind
  ; pol : ind
  ; psatz : ind
  ; proof : ind }

(* A registered constructor of each inductive type that the reader reads, its
   number of parameters and its constructor names, in the order of the
   constructors of the extracted types. *)
let lookup_ind env minds (name, np, consnames) =
  match Rocqlib.lib_ref_opt name with
  | Some (GlobRef.ConstructRef ((m, i) as ind, _)) ->
    if not (List.exists (MutInd.CanOrd.equal m) minds) then raise Reject;
    let mib = Environ.lookup_mind m env in
    let names = Array.map Id.to_string mib.mind_packets.(i).mind_consnames in
    if mib.mind_nparams <> np || names <> consnames then raise Reject;
    {ind; np}
  | _ -> raise Reject

let init env checker =
  let digest, opaque, minds = fingerprint env checker in
  debug (fun () ->
      Pp.(str "ZTautoChecker fingerprint " ++ str digest ++ str ", opaque constants " ++ int opaque));
  if not (String.equal digest expected_fingerprint && opaque = 0) then raise Reject;
  let ind = lookup_ind env minds in
  { pos = ind ("num.pos.xI", 0, [|"xI"; "xO"; "xH"|])
  ; z = ind ("num.Z.Z0", 0, [|"Z0"; "Zpos"; "Zneg"|])
  ; n = ind ("num.N.N0", 0, [|"N0"; "Npos"|])
  ; nat = ind ("num.nat.O", 0, [|"O"; "S"|])
  ; list = ind ("core.list.nil", 1, [|"nil"; "cons"|])
  ; option = ind ("core.option.None", 1, [|"Some"; "None"|])
  ; unit = ind ("core.unit.tt", 0, [|"tt"|])
  ; kind = ind ("micromega.kind.isProp", 0, [|"isProp"; "isBool"|])
  ; gform =
      ind ( "micromega.GFormula.TT", 4
          , [|"TT"; "FF"; "X"; "A"; "AND"; "OR"; "NOT"; "IMPL"; "IFF"; "EQ"|] )
  ; form = ind ("micromega.Formula.Build_Formula", 1, [|"Build_Formula"|])
  ; pexpr =
      ind ( "micromega.PExpr.PEc", 1
          , [|"PEc"; "PEX"; "PEadd"; "PEsub"; "PEmul"; "PEopp"; "PEpow"|] )
  ; op2 = ind ("micromega.Op2.OpEq", 0, [|"OpEq"; "OpNEq"; "OpLe"; "OpGe"; "OpLt"; "OpGt"|])
  ; pol = ind ("micromega.Pol.Pc", 1, [|"Pc"; "Pinj"; "PX"|])
  ; psatz =
      ind ( "micromega.Psatz.PsatzIn", 1
          , [| "PsatzLet"; "PsatzIn"; "PsatzSquare"; "PsatzMulC"; "PsatzMulE"
             ; "PsatzAdd"; "PsatzC"; "PsatzZ" |] )
  ; proof =
      ind ( "micromega.ZArithProof.DoneProof", 0
          , [| "DoneProof"; "RatProof"; "CutProof"; "SplitProof"; "deprecated_EnumProof"
             ; "ExProof" |] ) }

(* The reader works on [EConstr.t] in [(env, sigma)]: [EConstr.kind sigma] sees
   through defined evars, as the VM does (Genlambda expands them). The value of
   a variable is the value of its body, and the value of a cast is the value of
   its term, as in the VM (which erases casts). *)
let rec whd (env, sigma as gl) c =
  match EConstr.kind sigma c with
  | Var id -> (
    match Environ.lookup_named id env with
    | Context.Named.Declaration.LocalDef (_, b, _) -> whd gl (EConstr.of_constr b)
    | Context.Named.Declaration.LocalAssum _ -> raise Reject )
  | Cast (c, _, _) -> whd gl c
  | k -> k

(* [ctor gl i c] is [(j, args)] when [c] is the [j]th constructor of [i]
   applied to [args] (parameters first). *)
let ctor (_, sigma as gl) i c =
  match whd gl c with
  | Construct ((ind, j), _) when i.np = 0 && Ind.CanOrd.equal ind i.ind -> (j, [||])
  | App (f, args) -> (
    match EConstr.kind sigma f with
    | Construct ((ind, j), _)
      when Ind.CanOrd.equal ind i.ind && Array.length args >= i.np ->
      (j, args)
    | _ -> raise Reject )
  | _ -> raise Reject

(* [args i a n] checks that [a] has [n] arguments after the parameters. *)
let args i a n = Array.length a = i.np + n
let arg i a k = a.(i.np + k)

let rec read_pos gl st c =
  match ctor gl st.pos c with
  | 1, a when args st.pos a 1 -> Zc.XI (read_pos gl st (arg st.pos a 0))
  | 2, a when args st.pos a 1 -> Zc.XO (read_pos gl st (arg st.pos a 0))
  | 3, a when args st.pos a 0 -> Zc.XH
  | _ -> raise Reject

let read_z gl st c =
  match ctor gl st.z c with
  | 1, a when args st.z a 0 -> Zc.Z0
  | 2, a when args st.z a 1 -> Zc.Zpos (read_pos gl st (arg st.z a 0))
  | 3, a when args st.z a 1 -> Zc.Zneg (read_pos gl st (arg st.z a 0))
  | _ -> raise Reject

let read_n gl st c =
  match ctor gl st.n c with
  | 1, a when args st.n a 0 -> Zc.N0
  | 2, a when args st.n a 1 -> Zc.Npos (read_pos gl st (arg st.n a 0))
  | _ -> raise Reject

let read_nat gl st c =
  let rec count k c =
    match ctor gl st.nat c with
    | 1, a when args st.nat a 0 -> k
    | 2, a when args st.nat a 1 -> count (k + 1) (arg st.nat a 0)
    | _ -> raise Reject
  in
  let rec build k acc = if k = 0 then acc else build (k - 1) (Zc.S acc) in
  build (count 0 c) Zc.O

let read_list gl st read c =
  let rec loop acc c =
    match ctor gl st.list c with
    | 1, a when args st.list a 0 -> List.rev acc
    | 2, a when args st.list a 2 ->
      loop (read gl st (arg st.list a 0) :: acc) (arg st.list a 1)
    | _ -> raise Reject
  in
  loop [] c

let read_unit gl st c =
  match ctor gl st.unit c with
  | 1, a when args st.unit a 0 -> Zc.Tt
  | _ -> raise Reject

let read_kind gl st c =
  match ctor gl st.kind c with
  | 1, a when args st.kind a 0 -> Zc.IsProp
  | 2, a when args st.kind a 0 -> Zc.IsBool
  | _ -> raise Reject

let read_op2 gl st c =
  match ctor gl st.op2 c with
  | j, a when args st.op2 a 0 -> (
    match j with
    | 1 -> Zc.OpEq
    | 2 -> Zc.OpNEq
    | 3 -> Zc.OpLe
    | 4 -> Zc.OpGe
    | 5 -> Zc.OpLt
    | 6 -> Zc.OpGt
    | _ -> raise Reject )
  | _ -> raise Reject

let rec read_pexpr gl st c =
  let i = st.pexpr in
  let e a n = read_pexpr gl st (arg i a n) in
  match ctor gl i c with
  | 1, a when args i a 1 -> Zc.PEc (read_z gl st (arg i a 0))
  | 2, a when args i a 1 -> Zc.PEX (read_pos gl st (arg i a 0))
  | 3, a when args i a 2 -> Zc.PEadd (e a 0, e a 1)
  | 4, a when args i a 2 -> Zc.PEsub (e a 0, e a 1)
  | 5, a when args i a 2 -> Zc.PEmul (e a 0, e a 1)
  | 6, a when args i a 1 -> Zc.PEopp (e a 0)
  | 7, a when args i a 2 -> Zc.PEpow (e a 0, read_n gl st (arg i a 1))
  | _ -> raise Reject

let read_formula gl st c =
  let i = st.form in
  match ctor gl i c with
  | 1, a when args i a 3 ->
    { Zc.flhs = read_pexpr gl st (arg i a 0)
    ; Zc.fop = read_op2 gl st (arg i a 1)
    ; Zc.frhs = read_pexpr gl st (arg i a 2) }
  | _ -> raise Reject

(* The checker ignores the payload of [X]. The VM evaluates it: only a variable
   without a body is accepted, whose value is an accumulator. *)
let read_x (env, sigma) c =
  match EConstr.kind sigma c with
  | Var id -> (
    match Environ.lookup_named id env with
    | Context.Named.Declaration.LocalAssum _ -> Obj.repr ()
    | Context.Named.Declaration.LocalDef _ -> raise Reject )
  | _ -> raise Reject

let rec read_bf gl st c =
  let i = st.gform in
  let k a = read_kind gl st (arg i a 0) in
  let f a n = read_bf gl st (arg i a n) in
  match ctor gl i c with
  | 1, a when args i a 1 -> Zc.TT (k a)
  | 2, a when args i a 1 -> Zc.FF (k a)
  | 3, a when args i a 2 -> Zc.X (k a, read_x gl (arg i a 1))
  | 4, a when args i a 3 ->
    Zc.A (k a, read_formula gl st (arg i a 1), read_unit gl st (arg i a 2))
  | 5, a when args i a 3 -> Zc.AND (k a, f a 1, f a 2)
  | 6, a when args i a 3 -> Zc.OR (k a, f a 1, f a 2)
  | 7, a when args i a 2 -> Zc.NOT (k a, f a 1)
  | 8, a when args i a 4 ->
    let o =
      match ctor gl st.option (arg i a 2) with
      | 1, o when args st.option o 1 -> Some (read_unit gl st (arg st.option o 0))
      | 2, o when args st.option o 0 -> None
      | _ -> raise Reject
    in
    Zc.IMPL (k a, f a 1, o, f a 3)
  | 9, a when args i a 3 -> Zc.IFF (k a, f a 1, f a 2)
  | 10, a when args i a 2 -> Zc.EQ (f a 0, f a 1)
  | _ -> raise Reject

let rec read_pol gl st c =
  let i = st.pol in
  match ctor gl i c with
  | 1, a when args i a 1 -> Zc.Pc (read_z gl st (arg i a 0))
  | 2, a when args i a 2 -> Zc.Pinj (read_pos gl st (arg i a 0), read_pol gl st (arg i a 1))
  | 3, a when args i a 3 ->
    Zc.PX (read_pol gl st (arg i a 0), read_pos gl st (arg i a 1), read_pol gl st (arg i a 2))
  | _ -> raise Reject

let rec read_psatz gl st c =
  let i = st.psatz in
  let p a n = read_psatz gl st (arg i a n) in
  match ctor gl i c with
  | 1, a when args i a 2 -> Zc.PsatzLet (p a 0, p a 1)
  | 2, a when args i a 1 -> Zc.PsatzIn (read_nat gl st (arg i a 0))
  | 3, a when args i a 1 -> Zc.PsatzSquare (read_pol gl st (arg i a 0))
  | 4, a when args i a 2 -> Zc.PsatzMulC (read_pol gl st (arg i a 0), p a 1)
  | 5, a when args i a 2 -> Zc.PsatzMulE (p a 0, p a 1)
  | 6, a when args i a 2 -> Zc.PsatzAdd (p a 0, p a 1)
  | 7, a when args i a 1 -> Zc.PsatzC (read_z gl st (arg i a 0))
  | 8, a when args i a 0 -> Zc.PsatzZ
  | _ -> raise Reject

(* [deprecated_EnumProof] (constructor 5) is not read: the term is left to the VM. *)
let rec read_proof gl st c =
  let i = st.proof in
  let p a n = read_proof gl st (arg i a n) in
  match ctor gl i c with
  | 1, a when args i a 0 -> Zc.DoneProof
  | 2, a when args i a 2 -> Zc.RatProof (read_psatz gl st (arg i a 0), p a 1)
  | 3, a when args i a 2 -> Zc.CutProof (read_psatz gl st (arg i a 0), p a 1)
  | 4, a when args i a 3 -> Zc.SplitProof (read_pol gl st (arg i a 0), p a 1, p a 2)
  | 6, a when args i a 2 -> Zc.ExProof (read_pos gl st (arg i a 0), p a 1)
  | _ -> raise Reject

(** {1 The tactic} *)

(* The last declaration of [ZTautoChecker] checked, and the reader's state if it
   has the expected fingerprint. A declaration is never changed in place, and
   every declaration that it reaches was in the environment when it was added, so
   the same declaration object ([==]) has the same fingerprint. After [Reset] and
   a new [Require], Stdlib's declarations are read from disk again (perhaps from
   a Stdlib rebuilt in between), so the new object is checked again. *)
let state_memo = ref None

(* BET-84: a hit skips the reads of [fingerprint] (the declarations the
   checker reaches); while a proof is recorded the checker is checked again. *)
let state_for env checker =
  match Environ.lookup_constant_opt checker env with
  | None -> None
  | Some cb -> (
    let check () =
      try Some (init env checker) with
      | Reject ->
        debug (fun () ->
            Pp.str
              "ZTautoChecker refused: its fingerprint or the registered constructors are not the extraction's");
        None
      | e when CErrors.noncritical e ->
        debug (fun () -> Pp.(str "ZTautoChecker refused: " ++ CErrors.print e));
        None
    in
    if Proof_recorder.active () then check ()
    else
    match !state_memo with
    | Some (cb', st) when cb' == cb -> st
    | _ ->
      let st = check () in
      state_memo := Some (cb, st);
      st )

(* [Zchecker.zTautoChecker f w] is
     [tauto_checker zunsat zdeduce normalise negate (fun cl -> zChecker (map fst cl)) f w]
   (zchecker.ml); [z_tauto_checker] is the same with the pair checks of the CNF conversion
   computed once per pair of literals ([Cnf_memo] says why the result is the same). *)
module CnfZ = Cnf_memo.Make (struct
  type t = Zc.z Zc.nFormula

  let incompatible f f' =
    match Zc.zdeduce f f' with Some u -> Zc.zunsat u | None -> false
end)

let z_tauto_checker f w =
  let st = CnfZ.create () in
  Zc.tauto_checker CnfZ.unsat (CnfZ.deduce st)
    (fun x a -> CnfZ.tag st (Zc.normalise x a))
    (fun x a -> CnfZ.tag st (Zc.negate x a))
    (fun cl -> Zc.zChecker (Zc.map (fun (l, _) -> CnfZ.strip l) cl))
    f w

(* [holds gl st f w]: [Zchecker.zTautoChecker] on the values of [f] and [w];
   [false] if they cannot be read. *)
let holds gl st f w =
  match z_tauto_checker (read_bf gl st f) (read_list gl st read_proof w) with
  | b -> b
  | exception Stack_overflow -> false
  | exception e when CErrors.noncritical e -> false

(** Stdlib's [Lia.zchecker], which [lia] and [nia] pass to [xlia] and [xnia]:
{[
Ltac zchecker :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff ;
  exact (ZTautoChecker_sound __ff __wit
                                (@eq_refl bool true <: @eq bool (ZTautoChecker __ff __wit) true)
                                (@find Z Z0 __varmap)).
]}
   [zchecker_parts v] is [Some] when the tactic value [v] is a call of the global
   tactic [Stdlib.micromega.Lia.zchecker] with no local Ltac variables in its
   closure, and the MD5 of that tactic's body (marshalled without sharing) is
   [expected_zchecker]: the body above, as Stdlib 9.2.0's Lia.vo stores it. *)
let zchecker_path = "Stdlib.micromega.Lia.zchecker"

let expected_zchecker = "c8cd7b713edc9fed01c8c56d3fb2085f"

let zchecker_digest body =
  let d = Digest.to_hex (Digest.string (Marshal.to_string body [Marshal.No_sharing])) in
  debug (fun () -> Pp.(str "zchecker digest " ++ str d));
  d

(* The parts of [zchecker]'s body that the fast path uses: the names of its three
   Ltac variables ([__wit], [__varmap], [__ff]), the glob term of its [exact]
   split at the cast: the application with the cast replaced by a variable
   ([app h]), the term of the cast and its type, and the constant
   [ZTautoChecker] that the type of the cast applies. The fast path pretypes
   these glob terms, so its constr has the global references (kernel names
   included) of the glob term that [exact] pretypes. *)
type parts =
  { var_w : Id.t
  ; var_v : Id.t
  ; var_f : Id.t
  ; app : Id.t -> Glob_term.glob_constr
  ; cast_term : Glob_term.glob_constr
  ; cast_type : Glob_term.glob_constr
  ; checker : Constant.t }

let parts_of_body (body : Ltac_plugin.Tacexpr.glob_tactic_expr) =
  let open Ltac_plugin.Tacexpr in
  let fresh_let (b : glob_tactic_expr) =
    match b.CAst.v with
    | TacLetIn (false, [({CAst.v = Name id}, TacFreshId _)], rest) -> (id, rest)
    | _ -> raise Reject
  in
  let var_w, b = fresh_let body in
  let var_v, b = fresh_let b in
  let var_f, b = fresh_let b in
  (* [exact c] is the notation of the ML tactic [exact] of the Ltac plugin
     (plugins/ltac/coretactics.mlg): a [TacAlias] whose body calls that ML
     tactic. *)
  let is_exact kn =
    let open Ltac_plugin in
    Tacenv.check_alias kn
    &&
    match (Tacenv.interp_alias kn).Tacenv.alias_body.CAst.v with
    | TacML ({mltac_name = {mltac_plugin = "rocq-runtime.plugins.ltac"; mltac_tactic = "exact"}; mltac_index = 0}, [_]) -> true
    | _ -> false
  in
  let uconstr g =
    if Genarg.has_type g (Genarg.glbwit Stdarg.wit_uconstr) then
      match Genarg.out_gen (Genarg.glbwit Stdarg.wit_uconstr) g with
      | (c, None) -> c
      | (_, Some _) -> raise Reject
    else raise Reject
  in
  let g =
    match b.CAst.v with
    | TacThen ({CAst.v = TacAtom (TacIntroPattern (false, _))}, {CAst.v = TacAlias (kn, [TacGeneric (_, g)])})
      when is_exact kn -> uconstr g
    | _ -> raise Reject
  in
  (* The type of the cast: [@eq bool (ZTautoChecker __ff __wit) true]. *)
  let checker cast_type =
    match DAst.get cast_type with
    | Glob_term.GApp (_, [_; c; _]) -> (
      match DAst.get c with
      | Glob_term.GApp (f, [_; _]) -> (
        match DAst.get f with
        | Glob_term.GRef (GlobRef.ConstRef k, _) -> k
        | _ -> raise Reject )
      | _ -> raise Reject )
    | _ -> raise Reject
  in
  match DAst.get g with
  | Glob_term.GApp (f, [a1; a2; c; a4]) -> (
    match DAst.get c with
    | Glob_term.GCast (cast_term, Some VMcast, cast_type) ->
      let app h = DAst.make ?loc:g.CAst.loc (Glob_term.GApp (f, [a1; a2; DAst.make (Glob_term.GVar h); a4])) in
      {var_w; var_v; var_f; app; cast_term; cast_type; checker = checker cast_type}
    | _ -> raise Reject )
  | _ -> raise Reject

(* The last body checked and its parts. *)
let zchecker_memo = ref None

let zchecker_parts v =
  let open Ltac_plugin in
  let global_kn (body : Tacexpr.glob_tactic_expr) =
    match body.CAst.v with
    | Tacexpr.TacArg (Tacexpr.Reference (Locus.ArgArg (_, kn)))
    | Tacexpr.TacArg (Tacexpr.TacCall {CAst.v = (Locus.ArgArg (_, kn), [])}) -> Some kn
    | _ -> None
  in
  match Taccoerce.Value.to_tacvalue v with
  | Some (Taccoerce.VFun (_, _, _, lfun, [], body)) when Id.Map.is_empty lfun -> (
    match global_kn body with
    | Some kn when String.equal (KerName.to_string kn) zchecker_path -> (
      match Tacenv.interp_ltac kn with
      | exception Not_found -> None
      | body -> (
        let parts () =
          try
            if String.equal (zchecker_digest body) expected_zchecker then Some (parts_of_body body)
            else None
          with e when CErrors.noncritical e -> None
        in
        (* BET-84: a hit skips the tactic_alias reads of [parts_of_body]
           ([is_exact]); while a proof is recorded the body is read again. *)
        if Proof_recorder.active () then parts ()
        else
        match !zchecker_memo with
        | Some (b, r) when b == body -> r
        | _ ->
          let r = parts () in
          zchecker_memo := Some (body, r);
          r ) )
    | _ -> None )
  | _ -> None

(* Ltac's [fresh s] in [zchecker], where [avoid] holds the identifiers bound by
   the [let]s before it (Tacinterp.interp_fresh_id with an empty closure). The
   keyword test is Tacinterp's, which records it (BET-84 census row 17). *)
let fresh_name env avoid s =
  let s = if Ltac_plugin.Tacinterp.fresh_keyword s then s ^ "0" else s in
  Tactics.fresh_id_in_env avoid (Id.of_string s) env

exception Refused

(* [exact_term poly p ~ff ~wit ~vm env sigma concl]: the term that [zchecker]'s
   [exact] builds in the goal that its [intros] leaves, and the evar map that its
   pretyping returns, without the VM conversion of the cast. As in [exact], the
   glob terms are closed over [zchecker]'s Ltac variables, bound to the
   identifiers that [fresh] gave them ([Tacinterp.interp_uconstr]), and pretyped
   with Ltac's flags ([Tacinterp.type_uconstr]), in the order in which pretyping
   meets them in [exact]'s term: the type of the cast, its term (each application
   of the template inductive [eq] makes a universe variable), then the
   application, with the cast replaced by a hypothesis [h] of its type, against
   the conclusion. The cast node is then put in place of [h]. *)
let exact_term poly p ~ff ~wit ~vm env sigma concl =
  let open EConstr in
  let value id =
    Geninterp.Val.inject (Geninterp.val_tag (Genarg.topwit Ltac_plugin.Tacarg.wit_intropattern))
      (CAst.make (Tactypes.IntroNaming (Namegen.IntroIdentifier id)))
  in
  let lfun = Id.Map.(add p.var_w (value wit) (add p.var_v (value vm) (singleton p.var_f (value ff)))) in
  let ist = { Geninterp.lfun; poly; extra = Geninterp.TacStore.empty } in
  let understand expected_type env sigma g =
    let c = Ltac_plugin.Tacinterp.interp_uconstr ist env sigma (g, None) in
    Ltac_plugin.Tacinterp.type_uconstr ~expected_type ist c env sigma
  in
  let h =
    Namegen.next_ident_away (Id.of_string "__cast")
      (Id.Set.of_list (List.map Context.Named.Declaration.get_id (named_context env)))
  in
  let sigma, cast_type = understand Pretyping.IsType env sigma p.cast_type in
  let sigma, refl = understand Pretyping.WithoutTypeConstraint env sigma p.cast_term in
  let env_h =
    push_named
      (Context.Named.Declaration.LocalAssum (Context.make_annot h ERelevance.relevant, cast_type))
      env
  in
  let sigma, app = understand (Pretyping.OfType concl) env_h sigma (p.app h) in
  (sigma, Vars.replace_vars sigma [(h, mkCast (refl, VMcast, cast_type))] app)

(* [fast gl st p stock]: on the goal that [zchecker] receives,
     [let __wit := w in let __varmap := v in let __ff := f in concl],
   [Some tac] when the extracted checker returns [true] on the bodies of [__ff]
   and [__wit], which the VM evaluates; [None] otherwise. [tac] does what
   [zchecker] does: the same [intros], then [exact_term] and [exact_no_check].
   If [exact_term] fails, [tac] runs [stock] from the start. *)
let fast gl st p stock =
  let open EConstr in
  let open Proofview.Notations in
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let id_w = fresh_name env Id.Set.empty "__wit" in
  let id_v = fresh_name env (Id.Set.singleton id_w) "__varmap" in
  let id_f = fresh_name env (Id.Set.add id_v (Id.Set.singleton id_w)) "__ff" in
  match kind sigma concl with
  | LetIn (na_w, w, tw, c1) -> (
    match kind sigma c1 with
    | LetIn (na_v, v, tv, c2) -> (
      match kind sigma c2 with
      | LetIn (_, f, _, _) ->
        (* The context after [intros __wit __varmap __ff], as far as the bodies
           of [__ff] and [__wit] need it. *)
        let vw = mkVar id_w and vv = mkVar id_v in
        let def id na b t = Context.Named.Declaration.LocalDef (Context.map_annot (fun _ -> id) na, b, t) in
        let env' =
          env
          |> push_named (def id_w na_w w tw)
          |> push_named (def id_v na_v (Vars.subst1 vw v) (Vars.subst1 vw tv))
        in
        (* The VM cast: the VM compares [@eq bool true true] with the type of the
           cast; they are equal exactly when [ZTautoChecker] computes [true] on
           the bodies of [__ff] and [__wit]. *)
        if not (holds (env', sigma) st (Vars.substl [vv; vw] f) w) then None
        else
          let intro id = CAst.make (Tactypes.IntroNaming (Namegen.IntroIdentifier id)) in
          let exact =
            Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (_, poly) ->
            Proofview.Goal.enter (fun gl ->
                match
                  exact_term poly p ~ff:id_f ~wit:id_w ~vm:id_v (Proofview.Goal.env gl)
                    (Proofview.Goal.sigma gl) (Proofview.Goal.concl gl)
                with
                | sigma, term ->
                  Tacticals.tclTHEN (Proofview.Unsafe.tclEVARS sigma) (Tactics.exact_no_check term)
                | exception e when CErrors.noncritical e -> Proofview.tclZERO Refused)
          in
          Some
            (Proofview.tclORELSE
               (Tacticals.tclTHEN
                  (Tactics.intro_patterns false [intro id_w; intro id_v; intro id_f])
                  exact)
               (fun _ -> stock))
      | _ -> None )
    | _ -> None )
  | _ -> None

let checker ist v =
  let stock = Ltac_plugin.Tacinterp.tactic_of_value ist v in
  match zchecker_parts v with
  | None -> stock
  | Some _ when Ltac_plugin.Tacinterp.get_debug () <> Ltac_plugin.Tactic_debug.DebugOff
                || Profile_tactic.get_profiling () -> stock
  | Some p ->
    Proofview.Goal.enter (fun gl ->
        match state_for (Proofview.Goal.env gl) p.checker with
        | None -> stock
        | Some st -> (
          match fast gl st p stock with
          | Some tac -> tac
          | None -> stock
          | exception e when CErrors.noncritical e -> stock ))
