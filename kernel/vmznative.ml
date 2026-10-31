(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Native evaluation of binary-number operations in the bytecode machine.

   A constant is given a native implementation only when its definition is the
   one that implementation computes. "Its definition" means the computational
   skeleton of its body together with the skeletons of all the constants that
   body uses, and the declarations of the inductive types it matches on: the
   encoder below writes that skeleton out as a string, and the string must equal
   one this file holds. Types, universes, binder names and match predicates are
   left out of the encoding because the machine does not read them during
   reduction; everything the machine does read is in it.

   Nothing here consults a name, so a user definition that happens to be called
   Z.add, in a module called Stdlib.BinInt, is evaluated by the stock path
   unless it *is* the definition of Z.add. *)

open Names
open Constr
open Declarations

let debug = CDebug.create ~name:"vmznative" ()

let pinned_count = ref 0
let pinned () = !pinned_count

(* Test-only: when [ROCQ_VMZNATIVE_DUMP] names a file, every constant's full
   encoding is appended there raw (no pretty-printer, so nothing is wrapped),
   which is how test-suite/output/VmNativeArith.v regenerates the pinned
   strings below. The shipped reduction path never looks at this. *)
let dump_channel = lazy (
  match Sys.getenv_opt "ROCQ_VMZNATIVE_DUMP" with
  | None -> None
  | Some f -> Some (open_out_gen [Open_append; Open_creat] 0o644 f))
let dump name s =
  match Lazy.force dump_channel with
  | None -> ()
  | Some ch ->
    output_string ch (match name with Some kn -> Constant.to_string kn | None -> "<anonymous>");
    output_char ch '\t';
    output_string ch s; output_char ch '\n'; flush ch

(* -------------------------------------------------------------------------- *)
(* The inductive types the native code reads and writes.                       *)

(* The machine gives a constant constructor the rank of the constructor among
   the constant ones, and a non-constant constructor a block tag one above its
   rank among the non-constant ones, tag 0 being kept for accumulators
   (kernel/indtypes.ml, "Assigning VM tags to constructors"). The C code in
   kernel/byterun/rocq_interp.c decodes and builds values with exactly the
   tables below, so they are what this check is for. *)
let positive_reloc = [| (1, 1); (2, 1); (0, 0) |] (* xI, xO, xH *)
let z_reloc = [| (0, 0); (1, 1); (2, 1) |]        (* Z0, Zpos, Zneg *)

let check_reloc expected mip =
  let tbl = mip.mind_reloc_tbl in
  Int.equal (Array.length tbl) (Array.length expected)
  && (let ok = ref true in
      Array.iteri (fun i (t, a) ->
          let (t', a') = expected.(i) in
          if not (Int.equal t t' && Int.equal a a') then ok := false)
        tbl;
      !ok)

let check_shape env (mind, i) expected =
  Int.equal i 0
  && (match Environ.lookup_mind mind env with
      | exception Not_found -> false
      | mib ->
        Int.equal (Array.length mib.mind_packets) 1
        && Int.equal mib.mind_nparams 0
        && Int.equal mib.mind_nparams_rec 0
        && (match mib.mind_universes with Monomorphic -> true | _ -> false)
        && check_reloc expected mib.mind_packets.(0))

let constructor_types env (mind, _) =
  (Environ.lookup_mind mind env).mind_packets.(0).mind_user_lc

(* [positive] is: xI (_:positive) | xO (_:positive) | xH *)
let check_positive env ind =
  check_shape env ind positive_reloc
  && (let p = UnsafeMonomorphic.mkInd ind in
      let lc = constructor_types env ind in
      let rec_arg = mkProd (Context.anonR, p, p) in
      Constr.equal lc.(0) rec_arg
      && Constr.equal lc.(1) rec_arg
      && Constr.equal lc.(2) p)

(* [Z] is: Z0 | Zpos (_:positive) | Zneg (_:positive) *)
let check_z env ind pos =
  check_shape env ind z_reloc
  && (let z = UnsafeMonomorphic.mkInd ind in
      let p = UnsafeMonomorphic.mkInd pos in
      let lc = constructor_types env ind in
      let arg = mkProd (Context.anonR, p, z) in
      Constr.equal lc.(0) z
      && Constr.equal lc.(1) arg
      && Constr.equal lc.(2) arg)

(* -------------------------------------------------------------------------- *)
(* The canonical encoding of a definition closure.                             *)

exception Not_native
type state = {
  env : Environ.env;
  buf : Buffer.t;
  mutable pos_ind : inductive option;
  mutable z_ind : inductive option;
  mutable fuel : int;
  (* The expected encodings this body can still become, or [None] for a caller
     that wants the encoding whatever it is. The walk reads the bodies of every
     constant the body calls, and it runs at every constant's declaration, so a
     body that no expected encoding has as a prefix must stop at the character
     where it parts from all of them, not at its end. *)
  mutable cands : string list option;
}

let keep st pos n at =
  match st.cands with
  | None -> ()
  | Some cs ->
    (match List.filter (fun c -> String.length c >= pos + n && at c) cs with
     | [] -> raise Not_native
     | cs -> st.cands <- Some cs)

let put_char st ch =
  keep st (Buffer.length st.buf) 1 (fun c -> Char.equal c.[Buffer.length st.buf] ch);
  Buffer.add_char st.buf ch

let put st s =
  let pos = Buffer.length st.buf and n = String.length s in
  let at c =
    let rec eq i = i >= n || (Char.equal (String.unsafe_get c (pos + i)) (String.unsafe_get s i)
                              && eq (i + 1)) in
    eq 0
  in
  keep st pos n at;
  Buffer.add_string st.buf s

let add_int st i = put st (string_of_int i); put_char st ';'

(* 0 for [positive], 1 for [Z]; any other inductive stops the encoding. The
   first inductive of each kind that the body mentions fixes the one the whole
   definition must use, so a body that mixes two copies is refused. *)
let ind_code st ind =
  let same = function Some i -> Ind.CanOrd.equal i ind | None -> false in
  if same st.pos_ind then 0
  else if same st.z_ind then 1
  else if Option.is_empty st.pos_ind && check_positive st.env ind then
    (st.pos_ind <- Some ind; 0)
  else
    let pos = match st.pos_ind with
      | Some p -> Some p
      | None ->
        (* [Z]'s constructors name [positive]; take it from there. *)
        (match check_shape st.env ind z_reloc with
         | false -> None
         | true ->
           let lc = constructor_types st.env ind in
           (match kind lc.(1) with
            | Prod (_, dom, _) ->
              (match kind dom with
               | Ind (p, u) when UVars.Instance.is_empty u && check_positive st.env p ->
                 st.pos_ind <- Some p; Some p
               | _ -> None)
            | _ -> None))
    in
    match pos with
    | Some p when Option.is_empty st.z_ind && check_z st.env ind p ->
      st.z_ind <- Some ind; 1
    | _ -> raise Not_native

let rec encode st c =
  st.fuel <- st.fuel - 1;
  if st.fuel <= 0 then raise Not_native;
  match kind c with
  | Rel i -> put_char st 'R'; add_int st i
  | Lambda (_, _, b) -> put_char st 'L'; encode st b
  | LetIn (_, v, _, b) -> put_char st 'E'; encode st v; encode st b
  | App (f, args) ->
    put_char st 'A'; add_int st (Array.length args);
    encode st f; Array.iter (encode st) args
  | Const (kn, u) ->
    if not (UVars.Instance.is_empty u) then raise Not_native;
    put_char st 'C'; encode_const st kn
  | Ind (ind, u) ->
    if not (UVars.Instance.is_empty u) then raise Not_native;
    put_char st 'I'; add_int st (ind_code st ind)
  | Construct ((ind, j), u) ->
    if not (UVars.Instance.is_empty u) then raise Not_native;
    put_char st 'K'; add_int st (ind_code st ind); add_int st j
  | Case (ci, u, pms, _, iv, scrut, brs) ->
    if not (UVars.Instance.is_empty u) then raise Not_native;
    if not (Int.equal (Array.length pms) 0) then raise Not_native;
    (match iv with NoInvert -> () | CaseInvert _ -> raise Not_native);
    put_char st 'S';
    add_int st (ind_code st ci.ci_ind);
    add_int st ci.ci_npar;
    add_int st (Array.length brs);
    encode st scrut;
    Array.iter (fun (nas, b) -> add_int st (Array.length nas); encode st b) brs
  | Fix ((recidx, i), (_, _, bodies)) ->
    put_char st 'F'; add_int st i; add_int st (Array.length bodies);
    Array.iter (fun r -> add_int st r) recidx;
    Array.iter (encode st) bodies
  | Var _ | Meta _ | Evar _ | Sort _ | Cast _ | Prod _ | CoFix _ | Proj _
  | Int _ | Float _ | String _ | Array _ -> raise Not_native

and encode_const st kn =
  match Environ.lookup_constant kn st.env with
  | exception Not_found -> raise Not_native
  | cb ->
    (match cb.const_universes with Monomorphic -> () | Polymorphic _ -> raise Not_native);
    if cb.const_inline_code then raise Not_native;
    (match cb.const_body with
     | Def b -> encode st b
     | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> raise Not_native)

let encoding_of_body ?cands env body =
  let st = { env; buf = Buffer.create 4096; pos_ind = None; z_ind = None;
             fuel = 200000; cands } in
  (try encode st body; Some (Buffer.contents st.buf) with Not_native -> None)

let encoding env kn =
  match Environ.lookup_constant kn env with
  | exception Not_found -> None
  | cb ->
    (match cb.const_universes, cb.const_body with
     | Monomorphic, Def b -> encoding_of_body env b
     | _ -> None)

(* -------------------------------------------------------------------------- *)
(* The table of definitions with a native implementation.                      *)

(* Generated by printing [encoding] on the standard library's constant; see
   test-suite/output/VmNativeArith.v, which fails when the definition moves. *)
let expected = [
  "LLS1;0;3;R2;0;R1;1;S1;0;3;R2;0;R3;1;A1;K1;2;A2;CF0;2;0;0;LLS0;0;3;R2;1;S0;0;3;R2;1;A1;K0;2;A2;R5;R2;R1;1;A1;K0;1;A2;R6;R2;R1;0;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;S0;0;3;R2;1;A1;K0;1;A2;R6;R2;R1;1;A1;K0;2;A2;R6;R2;R1;0;A1;K0;1;R1;0;S0;0;3;R1;1;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;LLS0;0;3;R2;1;S0;0;3;R2;1;A1;K0;1;A2;R5;R2;R1;1;A1;K0;2;A2;R5;R2;R1;0;A1;K0;1;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;S0;0;3;R2;1;A1;K0;2;A2;R5;R2;R1;1;A1;K0;1;A2;R6;R2;R1;0;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;0;S0;0;3;R1;1;A1;K0;1;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;0;A1;K0;1;K0;3;R2;R1;1;A2;CF0;1;1;LLS0;0;3;R2;1;S0;0;3;R2;1;A1;CLS1;0;3;R1;0;K1;1;1;A1;K1;2;A1;K0;2;R1;1;A1;K1;3;A1;K0;2;R1;A2;R5;R2;R1;1;A1;CLS1;0;3;R1;0;A1;K1;2;K0;3;1;A1;K1;2;A1;K0;1;R1;1;A1;K1;3;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;A2;R5;R2;R1;0;A1;K1;2;A1;K0;2;R1;1;S0;0;3;R2;1;A1;CLS1;0;3;R1;0;A1;K1;3;K0;3;1;A1;K1;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;1;A1;K1;3;A1;K0;1;R1;A2;R5;R2;R1;1;A1;CLS1;0;3;R1;0;K1;1;1;A1;K1;2;A1;K0;2;R1;1;A1;K1;3;A1;K0;2;R1;A2;R5;R2;R1;0;A1;K1;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;0;S0;0;3;R1;1;A1;K1;3;A1;K0;2;R1;1;A1;K1;3;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;0;K1;1;R2;R1;1;S1;0;3;R2;0;R3;1;A2;CF0;1;1;LLS0;0;3;R2;1;S0;0;3;R2;1;A1;CLS1;0;3;R1;0;K1;1;1;A1;K1;2;A1;K0;2;R1;1;A1;K1;3;A1;K0;2;R1;A2;R5;R2;R1;1;A1;CLS1;0;3;R1;0;A1;K1;2;K0;3;1;A1;K1;2;A1;K0;1;R1;1;A1;K1;3;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;A2;R5;R2;R1;0;A1;K1;2;A1;K0;2;R1;1;S0;0;3;R2;1;A1;CLS1;0;3;R1;0;A1;K1;3;K0;3;1;A1;K1;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;1;A1;K1;3;A1;K0;1;R1;A2;R5;R2;R1;1;A1;CLS1;0;3;R1;0;K1;1;1;A1;K1;2;A1;K0;2;R1;1;A1;K1;3;A1;K0;2;R1;A2;R5;R2;R1;0;A1;K1;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;0;S0;0;3;R1;1;A1;K1;3;A1;K0;2;R1;1;A1;K1;3;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;0;K1;1;R1;R2;1;A1;K1;3;A2;CF0;2;0;0;LLS0;0;3;R2;1;S0;0;3;R2;1;A1;K0;2;A2;R5;R2;R1;1;A1;K0;1;A2;R6;R2;R1;0;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;S0;0;3;R2;1;A1;K0;1;A2;R6;R2;R1;1;A1;K0;2;A2;R6;R2;R1;0;A1;K0;1;R1;0;S0;0;3;R1;1;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;LLS0;0;3;R2;1;S0;0;3;R2;1;A1;K0;1;A2;R5;R2;R1;1;A1;K0;2;A2;R5;R2;R1;0;A1;K0;1;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;S0;0;3;R2;1;A1;K0;2;A2;R5;R2;R1;1;A1;K0;1;A2;R6;R2;R1;0;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;0;S0;0;3;R1;1;A1;K0;1;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;0;A1;K0;1;K0;3;R2;R1;", Vmbytecodes.ZNadd;
  "F0;1;1;LLS0;0;3;R2;1;S0;0;3;R2;1;A1;CLS1;0;3;R1;0;K1;1;1;A1;K1;2;A1;K0;2;R1;1;A1;K1;3;A1;K0;2;R1;A2;R5;R2;R1;1;A1;CLS1;0;3;R1;0;A1;K1;2;K0;3;1;A1;K1;2;A1;K0;1;R1;1;A1;K1;3;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;A2;R5;R2;R1;0;A1;K1;2;A1;K0;2;R1;1;S0;0;3;R2;1;A1;CLS1;0;3;R1;0;A1;K1;3;K0;3;1;A1;K1;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;1;A1;K1;3;A1;K0;1;R1;A2;R5;R2;R1;1;A1;CLS1;0;3;R1;0;K1;1;1;A1;K1;2;A1;K0;2;R1;1;A1;K1;3;A1;K0;2;R1;A2;R5;R2;R1;0;A1;K1;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;0;S0;0;3;R1;1;A1;K1;3;A1;K0;2;R1;1;A1;K1;3;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;1;A1;K0;2;R1;1;A1;K0;1;A1;R3;R1;0;K0;3;R1;0;K1;1;", Vmbytecodes.ZNpossub;
  "F0;2;0;0;LLS0;0;3;R2;1;S0;0;3;R2;1;A1;K0;2;A2;R5;R2;R1;1;A1;K0;1;A2;R6;R2;R1;0;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;S0;0;3;R2;1;A1;K0;1;A2;R6;R2;R1;1;A1;K0;2;A2;R6;R2;R1;0;A1;K0;1;R1;0;S0;0;3;R1;1;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;LLS0;0;3;R2;1;S0;0;3;R2;1;A1;K0;1;A2;R5;R2;R1;1;A1;K0;2;A2;R5;R2;R1;0;A1;K0;1;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;S0;0;3;R2;1;A1;K0;2;A2;R5;R2;R1;1;A1;K0;1;A2;R6;R2;R1;0;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;0;S0;0;3;R1;1;A1;K0;1;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;1;A1;K0;2;A1;CF0;1;0;LS0;0;3;R1;1;A1;K0;2;A1;R3;R1;1;A1;K0;1;R1;0;A1;K0;2;K0;3;R1;0;A1;K0;1;K0;3;", Vmbytecodes.ZNposadd;
]

(* The decision is taken where the body is compiled, so it is the decision for
   that very body: a redefinition (after [Reset], or a reused name) compiles
   its own body and gets its own answer. Nothing is cached by name, which
   would outlive the definition it was computed for.

   Every constant's declaration asks this, so the walk carries the expected
   encodings and stops at the first character that parts from all of them.
   With the dump channel on it carries none, because the point of the dump is
   the encoding of a definition that no longer matches.

   [name] is only printed. The line is one short line per declaration, which
   test-suite/output/VmNativeArith.v reads; the encoding itself goes to the
   dump channel, which is the tool for finding out why a definition is not
   pinned. *)
let expected_strings = lazy (List.map fst expected)

let pin_of_body ?name env body =
  let cands =
    if Option.has_some (Lazy.force dump_channel) then None
    else Some (Lazy.force expected_strings)
  in
  let r = match encoding_of_body ?cands env body with
    | None -> None
    | Some s ->
      dump name s;
      let rec find = function
        | [] -> None
        | (s', op) :: rest -> if String.equal s s' then Some op else find rest
      in
      find expected
  in
  debug Pp.(fun () ->
      (match name with Some kn -> Constant.print kn | None -> str "<anonymous>") ++
      (match r with
       | Some ZNadd -> str " native add"
       | Some ZNpossub -> str " native pos_sub"
       | Some ZNposadd -> str " native pos_add"
       | None -> str " interpreted"));
  (match r with Some _ -> incr pinned_count | None -> ());
  r
