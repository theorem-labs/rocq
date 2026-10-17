(* Experimental VM fast paths for closed Corelib binary-number operations.

   The C interpreter calls [eval] only after selecting one of the registered, root-owned Corelib/Stdlib
   closures by identity. Every operation is conservative: if an input is not an entirely constructor-built
   value, [Fallback] makes the interpreter use the original bytecode closure instead. *)

open Declarations

type operation =
  | Pos_compare_cont
  | Pos_eqb
  | Pos_add
  | Pos_mul
  | Z_pos_sub
  | Z_mul
  | Z_compare
  | Z_eqb
  | Z_leb
  | Z_ltb
  | Nat_eqb
  | Nat_leb

let enabled = Sys.getenv_opt "ROCQ_VM_FASTBIN" = Some "1"

let anchors = [
  "Corelib.BinNums.PosDef.Pos.compare_cont", Pos_compare_cont;
  "Corelib.BinNums.PosDef.Pos.eqb", Pos_eqb;
  "Corelib.BinNums.PosDef.Pos.add", Pos_add;
  "Corelib.BinNums.PosDef.Pos.mul", Pos_mul;
  "Corelib.BinNums.IntDef.Z.pos_sub", Z_pos_sub;
  "Corelib.BinNums.IntDef.Z.mul", Z_mul;
  "Corelib.BinNums.IntDef.Z.compare", Z_compare;
  "Corelib.BinNums.IntDef.Z.eqb", Z_eqb;
  "Corelib.BinNums.IntDef.Z.leb", Z_leb;
  "Corelib.BinNums.IntDef.Z.ltb", Z_ltb;
  "Corelib.Init.Nat.eqb", Nat_eqb;
  "Corelib.Init.Nat.leb", Nat_leb;
]

let references : (operation, Constr.t) Hashtbl.t = Hashtbl.create (List.length anchors)

let id = function
  | Pos_compare_cont -> 0
  | Pos_eqb -> 1
  | Pos_add -> 2
  | Pos_mul -> 3
  | Z_pos_sub -> 4
  | Z_mul -> 5
  | Z_compare -> 6
  | Z_eqb -> 7
  | Z_leb -> 8
  | Z_ltb -> 9
  | Nat_eqb -> 10
  | Nat_leb -> 11

let arity = function
  | Pos_compare_cont -> 3
  | Pos_eqb | Pos_add | Pos_mul | Z_pos_sub | Z_mul | Z_compare | Z_eqb | Z_leb | Z_ltb
  | Nat_eqb | Nat_leb -> 2

external register_closure : Vmvalues.values -> int -> int -> unit = "rocq_vmfast_register"

let capture_reference kn = function
  | Def body ->
    let name = Names.Constant.to_string kn in
    List.iter (fun (anchor, op) ->
        if String.equal name anchor && not (Hashtbl.mem references op) then
          Hashtbl.add references op body)
      anchors
  | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> ()

let operation_of_body body =
  Hashtbl.fold (fun op reference found ->
      match found with
      | Some _ -> found
      | None -> if Constr.equal body reference then Some op else None)
    references None

let register kn body value =
  if enabled then
    match operation_of_body body with
    | Some Pos_compare_cont | None -> ()
    | Some op -> register_closure value (id op) (arity op)

exception Fallback
let trace = Sys.getenv_opt "ROCQ_VM_FASTBIN_TRACE" = Some "1"

let fail kind =
  if trace then Printf.eprintf "FASTBIN fallback: %s\n%!" kind;
  raise Fallback

let int v = if Obj.is_int (Obj.repr v) then Some (Obj.magic v : int) else None
let value_int n : Vmvalues.values = Obj.magic n

(* VM constructor tags reserve zero for the accumulator branch. xI/xO are therefore 1/2. *)
let pos_bits (v : Vmvalues.values) =
  let rec loop v acc =
    match int v with
    | Some 0 -> List.rev (true :: acc)
    | Some _ -> fail "positive immediate"
    | None ->
      let o = Obj.repr v in
      if Obj.size o <> 1 then fail "positive size";
      match Obj.tag o with
      | 1 -> loop (Obj.obj (Obj.field o 0)) (true :: acc)
      | 2 -> loop (Obj.obj (Obj.field o 0)) (false :: acc)
      | tag -> fail ("positive tag " ^ string_of_int tag)
  in
  loop v []

let pos_of_bits bits : Vmvalues.values =
  match List.rev bits with
  | true :: bits ->
    List.fold_left (fun acc bit ->
        let o = Obj.new_block (if bit then 1 else 2) 1 in
        Obj.set_field o 0 (Obj.repr acc);
        Obj.obj o) (value_int 0) bits
  | _ -> raise Fallback

let compare_bits x y =
  let lx = List.length x and ly = List.length y in
  if lx < ly then -1 else if lx > ly then 1 else
  let rec loop x y =
    match x, y with
    | [], [] -> 0
    | x :: xs, y :: ys -> let c = loop xs ys in if c <> 0 then c else Bool.compare x y
    | _ -> assert false
  in loop x y

let bool b = value_int (if b then 0 else 1)
let comparison = function -1 -> value_int 1 | 0 -> value_int 0 | 1 -> value_int 2 | _ -> assert false

let add_bits x y =
  let rec loop x y carry acc =
    match x, y with
    | [], [] -> if carry then List.rev (true :: acc) else List.rev acc
    | xb :: xs, [] | [], xb :: xs ->
      let s = (if xb then 1 else 0) + if carry then 1 else 0 in
      loop xs [] (s >= 2) ((s land 1 = 1) :: acc)
    | xb :: xs, yb :: ys ->
      let s = (if xb then 1 else 0) + (if yb then 1 else 0) + if carry then 1 else 0 in
      loop xs ys (s >= 2) ((s land 1 = 1) :: acc)
  in loop x y false []

let rec zero_bits n =
  if n = 0 then [] else false :: zero_bits (n - 1)

let mul_bits x y =
  let rec loop x shift acc =
    match x with
    | [] -> acc
    | bit :: xs ->
      let acc = if bit then add_bits acc (zero_bits shift @ y) else acc in
      loop xs (shift + 1) acc
  in loop x 0 []

type z = Zero | Pos of bool list | Neg of bool list

let z_of_value (v : Vmvalues.values) =
  match int v with
  | Some 0 -> Zero
  | Some _ -> raise Fallback
  | None ->
    let o = Obj.repr v in
    if Obj.size o <> 1 then raise Fallback;
    match Obj.tag o with
    | 1 -> Pos (pos_bits (Obj.obj (Obj.field o 0)))
    | 2 -> Neg (pos_bits (Obj.obj (Obj.field o 0)))
    | _ -> raise Fallback

let z_of_signed sign bits =
  match bits with
  | [] -> value_int 0
  | _ ->
    let p = pos_of_bits bits in
    let o = Obj.new_block (if sign >= 0 then 1 else 2) 1 in
    Obj.set_field o 0 (Obj.repr p);
    Obj.obj o

let z_compare x y =
  match x, y with
  | Zero, Zero -> 0
  | Zero, Pos _ | Neg _, Zero | Neg _, Pos _ -> -1
  | Zero, Neg _ | Pos _, Zero | Pos _, Neg _ -> 1
  | Pos x, Pos y -> compare_bits x y
  | Neg x, Neg y -> - compare_bits x y

let sub_bits x y =
  let rec loop x y borrow acc =
    match x, y with
    | [], [] -> if borrow then raise Fallback else List.rev acc
    | xb :: xs, [] ->
      let d = (if xb then 1 else 0) - if borrow then 1 else 0 in
      loop xs [] (d < 0) ((d land 1 = 1) :: acc)
    | xb :: xs, yb :: ys ->
      let d = (if xb then 1 else 0) - (if yb then 1 else 0) - if borrow then 1 else 0 in
      loop xs ys (d < 0) ((d land 1 = 1) :: acc)
    | [], _ -> raise Fallback
  in
  let rec trim = function false :: xs -> trim xs | x -> x in
  List.rev (trim (List.rev (loop x y false [])))

let nat_count (v : Vmvalues.values) =
  let rec loop v n =
    match int v with
    | Some 0 -> n
    | Some _ -> raise Fallback
    | None ->
      let o = Obj.repr v in
      if Obj.tag o <> 1 || Obj.size o <> 1 || n = max_int then raise Fallback;
      loop (Obj.obj (Obj.field o 0)) (n + 1)
  in loop v 0

let eval2 op a b =
  try
    let args : Vmvalues.values array = [|Obj.magic a; Obj.magic b; Obj.magic ()|] in
    let result = match op, args with
      | 0, [|r; x; y|] ->
        let c = compare_bits (pos_bits x) (pos_bits y) in if c = 0 then r else comparison c
      | 1, [|x; y; _|] -> bool (compare_bits (pos_bits x) (pos_bits y) = 0)
      | 2, [|x; y; _|] -> pos_of_bits (add_bits (pos_bits x) (pos_bits y))
      | 3, [|x; y; _|] -> pos_of_bits (mul_bits (pos_bits x) (pos_bits y))
      | 4, [|x; y; _|] ->
        let x, y = pos_bits x, pos_bits y in
        let c = compare_bits x y in
        if c = 0 then value_int 0 else z_of_signed c (if c > 0 then sub_bits x y else sub_bits y x)
      | 5, [|x; y; _|] ->
        begin match z_of_value x, z_of_value y with
        | Zero, _ | _, Zero -> value_int 0
        | Pos x, Pos y | Neg x, Neg y -> z_of_signed 1 (mul_bits x y)
        | Pos x, Neg y | Neg x, Pos y -> z_of_signed (-1) (mul_bits x y)
        end
      | 6, [|x; y; _|] -> comparison (z_compare (z_of_value x) (z_of_value y))
      | 7, [|x; y; _|] -> bool (z_compare (z_of_value x) (z_of_value y) = 0)
      | 8, [|x; y; _|] -> bool (z_compare (z_of_value x) (z_of_value y) <= 0)
      | 9, [|x; y; _|] -> bool (z_compare (z_of_value x) (z_of_value y) < 0)
      | 10, [|x; y; _|] -> bool (Int.equal (nat_count x) (nat_count y))
      | 11, [|x; y; _|] -> bool (nat_count x <= nat_count y)
      | _ -> fail "operation arity"
    in
    Some (Obj.repr result)
  with Fallback -> None

let () = Callback.register "rocq_vm_fastbin2" eval2
