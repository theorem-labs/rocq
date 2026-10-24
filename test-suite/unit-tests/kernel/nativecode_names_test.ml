(* While coqchk decides VM casts with native code
   ([Nativecode.set_native_vm_conversion true]), the OCaml name that the
   native compiler gives to a global is injective on the whole kernel
   name, and the printed code takes no byte of a name outside
   [A-Za-z0-9_]. coqchk reads its names from .vo files, which may hold
   any bytes, so the names below are built at the OCaml level: the
   parser would refuse most of them. *)

open OUnit
open Utest
open Names

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let id = Id.of_string

(* An identifier with arbitrary bytes, as a .vo file can hold it:
   [Id.t] is a string that [Id.of_string] would check. *)
let raw_id (s : string) : Id.t = Obj.magic s

let top = ModPath.MPfile (DirPath.make [id "Top"])

let flags = Declareops.safe_flags Conv_oracle.empty

let body def = {
  Declarations.const_hyps = [];
  const_univ_hyps = UVars.Instance.empty;
  const_body = def;
  const_type = Constr.mkProp;
  const_relevance = Sorts.Relevant;
  const_body_code = None;
  const_universes = Declarations.Monomorphic;
  const_inline_code = false;
  const_typing_flags = flags;
}

let axiom = body (Declarations.Undef None)

(* The OCaml code that the native compiler prints for constant [c]. *)
let printed c cb =
  let cenv = Nativecode.make_cenv () in
  let code = Nativecode.compile_constant_field cenv Environ.empty_env c [] cb in
  String.concat "" (List.map (Format.asprintf "%a" Nativecode.pp_global) code)

let find_sub text sub =
  let n = String.length text and m = String.length sub in
  let rec go i =
    if i + m > n then None
    else if String.equal (String.sub text i m) sub then Some i
    else go (i + 1)
  in
  go 0

let contains text sub = Option.has_some (find_sub text sub)

let is_ident_char = function
  | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' -> true
  | _ -> false

(* The name that the printed definition of a constant binds, and the
   three bytes after it. *)
let defined_name text =
  match find_sub text "let const_" with
  | None -> assert_failure ("no constant definition in: " ^ text)
  | Some i ->
    let start = i + String.length "let " in
    let stop = ref start in
    while !stop < String.length text && is_ident_char text.[!stop] do incr stop done;
    let next = String.sub text !stop (min 3 (String.length text - !stop)) in
    String.sub text start (!stop - start), next

let name_of c = fst (defined_name (printed c axiom))

let with_switch b f =
  let saved = Nativecode.native_vm_conversion () in
  Nativecode.set_native_vm_conversion b;
  Fun.protect ~finally:(fun () -> Nativecode.set_native_vm_conversion saved) f

(* OCaml syntax that would end the name, open a comment and a string. *)
let payload = "x) (* \" y"

let () = add_test "a label holding OCaml syntax is escaped in the name" (fun () ->
  with_switch true (fun () ->
    let c = Constant.make2 top (raw_id payload) in
    let text = printed c axiom in
    let name, next = defined_name text in
    assert_equal ~msg:("the name ends inside the label: " ^ text) ~printer:(fun s -> s)
      " : " next;
    assert_bool ("the label's bytes reach the code: " ^ name)
      (not (contains text "(*") && not (contains text "\""))))

let () = add_test "A_B.c and A.B_c get different names" (fun () ->
  with_switch true (fun () ->
    let c1 = Constant.make2 (ModPath.MPdot (top, id "A_B")) (id "c") in
    let c2 = Constant.make2 (ModPath.MPdot (top, id "A")) (id "B_c") in
    let n1 = name_of c1 and n2 = name_of c2 in
    assert_bool (Printf.sprintf "both are named %s" n1) (not (String.equal n1 n2))))

let () = add_test "functor parameters with one Id and different integers get different names" (fun () ->
  with_switch true (fun () ->
    let dp = DirPath.make [id "Top"] in
    let x1 = MBId.make dp (id "X") and x2 = MBId.make dp (id "X") in
    let (i1, _, _) = MBId.repr x1 and (i2, _, _) = MBId.repr x2 in
    assert_bool "MBId.make gave one integer twice" (not (Int.equal i1 i2));
    let c1 = Constant.make2 (ModPath.MPbound x1) (id "f") in
    let c2 = Constant.make2 (ModPath.MPbound x2) (id "f") in
    let n1 = name_of c1 and n2 = name_of c2 in
    assert_bool (Printf.sprintf "both are named %s" n1) (not (String.equal n1 n2))))

let () = add_test "a binder name holding OCaml syntax is escaped" (fun () ->
  with_switch true (fun () ->
    let annot = Context.make_annot (Name.Name (raw_id payload)) Sorts.Relevant in
    let def = Constr.mkLambda (annot, Constr.mkProp, Constr.mkRel 1) in
    let c = Constant.make2 top (id "f") in
    let text = printed c (body (Declarations.Def def)) in
    assert_bool ("the binder name's bytes reach the code: " ^ text)
      (not (contains text "(*") && not (contains text "\""))))

let () = add_test "a primitive string reaches the code only as hexadecimal escapes" (fun () ->
  with_switch true (fun () ->
    let s = Pstring.unsafe_of_string payload in
    let c = Constant.make2 top (id "s") in
    let text = printed c (body (Declarations.Def (Constr.mkString s))) in
    assert_bool ("the string's bytes reach the code: " ^ text)
      (not (contains text "(*") && not (contains text "y\""))))

(* [Safe_typing.import] marks the globals of a library [Linked] to this
   prefix; coqchk never loads such a unit, but the prefix still follows the
   rules of the names. *)
let () = add_test "library prefixes are injective and escaped" (fun () ->
  with_switch true (fun () ->
    let uid l = Nativecode.mod_uid_of_dirpath (DirPath.make (List.rev_map raw_id l)) in
    let joined = uid ["A"; "B"] and underscored = uid ["A_B"] in
    assert_bool (Printf.sprintf "A.B and A_B both give %s" joined)
      (not (String.equal joined underscored));
    let evil = uid [payload] in
    assert_bool ("the dirpath's bytes reach the prefix: " ^ evil)
      (String.for_all is_ident_char evil)))

let () = add_test "with the switch off, names are today's" (fun () ->
  with_switch false (fun () ->
    let c = Constant.make2 (ModPath.MPdot (top, id "A_B")) (id "c") in
    assert_equal ~printer:(fun s -> s) "const_NTop_A_B_c" (name_of c);
    assert_equal ~printer:(fun s -> s) "NCorelib_Init_Nat"
      (Nativecode.mod_uid_of_dirpath (DirPath.make (List.rev_map id ["Corelib"; "Init"; "Nat"])))))

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
