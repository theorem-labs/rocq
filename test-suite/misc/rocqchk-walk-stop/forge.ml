(* Give Stops.vo one of the shapes coqc refuses to write, each a stop of
   the -o walk (checker/mod_impl.ml). Stops.v says which modules each shape
   changes:
     alias-cycle             Self := Self
     alias-two-cycle         Ping := Pong, Pong := Ping
     implementation-cycle    Up := Down, Down := Up.C
     functor-implementation  NotF := (functor) Defines
     with-functor            RW := (F with Module ... := A) A
     expression-arguments    Gexpr := (functor) (functor) F X
     path-chain              Chain.M := Chain, Chain.G := (functor) X.M.G X.M
     argument-chain          G := G A
   The file is rewritten in place. The helpers, and the value layouts they
   rely on, are those of misc/rocqchk_forge_lib.ml. This file adds
   checker/values.ml's layouts of what an Algebraic implementation (tag 0)
   holds, [expression]; of an expression MENoFunctor (tag 0) [algebraic
   expression] | MEMoreFunctor (tag 1) [expression]; of an algebraic
   expression MEident (tag 0) [module path] | MEapply (tag 1) [algebraic
   expression; module path] | MEwith (tag 2) [algebraic expression;
   with_declaration]; of a with_declaration WithMod (tag 0) [label list;
   module path]; and of a module path MPfile (tag 0) [dirpath] | MPbound
   (tag 1) [bound name] | MPdot (tag 2) [module path; label]. Each block is
   checked to have the expected shape before it is used.

   Command:
     forge.ml SHAPE STOPS.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

let dot mp label = block 2 [| mp; Obj.repr label |]

(* The expression of the module_body [mb]: field 0 is the implementation
   wrapper (tag 0) [implementation], here Algebraic [expression]. *)
let expression what mb =
  let wrapper = field mb 0 in
  expect ~size:1 (what ^ "'s implementation wrapper") 0 wrapper;
  let impl = field wrapper 0 in
  expect ~size:1 (what ^ "'s implementation (Algebraic)") 0 impl;
  field impl 0

(* The algebraic expression under MENoFunctor. *)
let no_functor what e =
  expect ~size:1 (what ^ " (MENoFunctor)") 0 e;
  field e 0

(* The path of an MEident. *)
let ident what a =
  expect ~size:1 (what ^ " (MEident)") 0 a;
  field a 0

(* The head and the argument of an MEapply. *)
let apply what a =
  expect ~size:2 (what ^ " (MEapply)") 1 a;
  field a 0, field a 1

let me_no_functor a = block 0 [| a |]
let me_more_functor e = block 1 [| e |]
let me_ident mp = block 0 [| mp |]
let me_apply head mp = block 1 [| head; mp |]
let me_with head decl = block 2 [| head; decl |]
let with_mod labels mp = block 0 [| labels; mp |]

(* [struc] with the module [name]'s expression replaced by [e]: the fields 0
   of SFBmodule, of module_body and of the wrapper. Only the blocks above
   the new expression are copied. *)
let set_expression struc name e = struc_update struc name (upd 0 (upd 0 (set 0 (block 0 [| e |]))))

(* [struc] with the alias [name] made an alias of [target]. *)
let alias struc name target =
  ignore (ident (name ^ "'s expression")
            (no_functor (name ^ "'s expression") (expression name (module_of struc name))));
  set_expression struc name (me_no_functor (me_ident target))

let forge shape disk =
  let root = root_struc disk in
  (* The library's path, the root of A's, which RW's expression names. *)
  let rw = expression "RW" (module_of root "RW") in
  let f_head, a = apply "RW's expression" (no_functor "RW's expression" rw) in
  expect ~size:2 "A's path (MPdot)" 2 a;
  let file = field a 0 in
  expect ~size:1 "the library's path (MPfile)" 0 file;
  let root =
    match shape with
    | "alias-cycle" -> alias root "Self" (dot file "Self")
    | "alias-two-cycle" -> alias (alias root "Ping" (dot file "Pong")) "Pong" (dot file "Ping")
    | "implementation-cycle" ->
      alias (alias root "Up" (dot file "Down")) "Down" (dot (dot file "Up") "C")
    | "functor-implementation" ->
      let e = expression "NotF" (module_of root "NotF") in
      ignore (no_functor "NotF's expression" e);
      set_expression root "NotF" (me_more_functor e)
    | "with-functor" ->
      ignore (ident "RW's head" f_head);
      set_expression root "RW" (me_no_functor (me_apply (me_with f_head (with_mod empty a)) a))
    | "expression-arguments" ->
      let e = expression "Gexpr" (module_of root "Gexpr") in
      expect ~size:1 "Gexpr's expression (MEMoreFunctor)" 1 e;
      set_expression root "Gexpr" (me_more_functor e)
    | "path-chain" ->
      (* Chain is declared without a type: its implementation is FullStruct
         (the immediate 1), and its structure is its signature's. *)
      let i = impl_of (module_of root "Chain") in
      if is_block i || to_int i <> 1 then fail "Chain's implementation is %s" (impl_kind i);
      let chain = alias (sig_struc root "Chain") "M" (dot file "Chain") in
      let e = expression "Chain.G" (module_of chain "G") in
      expect ~size:1 "G's expression (MEMoreFunctor)" 1 e;
      let head, x = apply "G's body" (no_functor "G's body" (field e 0)) in
      ignore (ident "G's head" head);
      expect ~size:1 "G's argument X (MPbound)" 1 x;
      let xm = dot x "M" in
      let chain =
        set_expression chain "G" (me_more_functor (me_no_functor (me_apply (me_ident (dot xm "G")) xm)))
      in
      struc_update root "Chain" (upd 0 (upd 1 (set 0 chain)))
    | "argument-chain" ->
      let head, arg = apply "G's expression" (no_functor "G's expression" (expression "G" (module_of root "G"))) in
      ignore (ident "G's head" head);
      set_expression root "G" (me_no_functor (me_apply (me_ident (dot file "G")) arg))
    | _ -> fail "unknown shape %s" shape
  in
  say "forge: %s" shape;
  set_root_struc disk root;
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ shape; file ] -> rewrite_vo ~src:file ~dst:file [ "library", forge shape ]
  | _ ->
    prerr_endline "usage: forge.ml SHAPE STOPS.vo";
    exit 2
