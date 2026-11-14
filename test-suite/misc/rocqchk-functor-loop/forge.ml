(* Give Loop.vo the functor coqc refuses to write: in the body of F, the
   module Grow, an application of G in the honest file, becomes an
   application of F itself.
     Grow := F Loc
   The type of R := F A is F's body substituted, and the substitution keeps
   the unchanged head of the application, MEident G, as the very block of
   F's body, so R's Grow shares F's head. The forgery gives both the same
   new head, so R's type says F too. The file is rewritten in place.

   The helpers, and the value layouts they rely on, are those of
   misc/rocqchk_forge_lib.ml. This file adds checker/values.ml's layouts of
   what an Algebraic implementation holds, [expression], of an expression
   MENoFunctor (tag 0) [algebraic expression], of an algebraic expression
   MEident (tag 0) [module path] | MEapply (tag 1) [head; argument], and of
   a module path MPfile (tag 0) [dirpath] | MPbound (tag 1) | MPdot (tag 2)
   [module path; label]. Each block is checked to have the expected shape
   before it is used.

   Command:
     forge.ml LOOP.vo *)

#use "./misc/rocqchk_forge_lib.ml";;

(* The structure of the body of the functor F, which the honest file
   declares without an ascription: its implementation is FullStruct (the
   immediate 1), and its signature, module_body field 1, is MoreFunctor
   (tag 1) [mbid; parameter type; NoFunctor (tag 0) [structure]]. *)
let functor_body mb =
  let wrapper = field mb 0 in
  expect ~size:1 "F's implementation wrapper" 0 wrapper;
  let impl = field wrapper 0 in
  if is_block impl || to_int impl <> 1 then fail "F's implementation is not FullStruct";
  let sign = field mb 1 in
  expect ~size:3 "F's signature (MoreFunctor)" 1 sign;
  let body = field sign 2 in
  expect ~size:1 "F's body (NoFunctor)" 0 body;
  field body 0

(* The MEident block at the head of the application that is the expression
   of [mb]: the implementation wrapper (tag 0) [implementation], Algebraic
   [expression], MENoFunctor [algebraic expression], MEapply [head;
   argument], and the head MEident [module path]. *)
let application_head what mb =
  let wrapper = field mb 0 in
  expect ~size:1 (what ^ "'s implementation wrapper") 0 wrapper;
  let impl = field wrapper 0 in
  expect ~size:1 (what ^ "'s implementation (Algebraic)") 0 impl;
  let me = field impl 0 in
  expect ~size:1 (what ^ "'s expression (MENoFunctor)") 0 me;
  let app = field me 0 in
  expect ~size:2 (what ^ "'s expression (MEapply)") 1 app;
  let head = field app 0 in
  expect ~size:1 (what ^ "'s head (MEident)") 0 head;
  head

(* [mb] with the head of its application replaced by [head]: the fields 0
   of module_body, wrapper, Algebraic and MENoFunctor, then MEapply's. *)
let with_head head = upd 0 (upd 0 (upd 0 (upd 0 (set 0 head))))

let forge disk =
  let root = root_struc disk in
  let body = functor_body (module_of root "F") in
  let rstruc = sig_struc root "R" in
  let head = application_head "Grow" (module_of body "Grow") in
  if application_head "Grow" (module_of rstruc "Grow") != head then
    fail "R's Grow does not share the head of F's";
  let g = field head 0 in
  expect ~size:2 "G's path (MPdot)" 2 g;
  let label = field g 1 in
  if Obj.is_int label || tag label <> Obj.string_tag || not (String.equal (to_str label) "G") then
    fail "Grow does not apply G";
  (* The new head names F's path: G's, with the label F. F's Grow and R's
     share it: only the blocks above it are copied in each, up to the
     library's root structure. *)
  let head = set 0 (set 1 (Obj.repr "F") g) head in
  let body = struc_update body "Grow" (upd 0 (with_head head)) in
  let rstruc = struc_update rstruc "Grow" (upd 0 (with_head head)) in
  say "forge: Grow now applies F";
  let root = struc_update root "F" (upd 0 (upd 1 (upd 2 (set 0 body)))) in
  let root = struc_update root "R" (upd 0 (upd 1 (set 0 rstruc))) in
  set_root_struc disk root;
  disk

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ file ] -> rewrite_vo ~src:file ~dst:file [ "library", forge ]
  | _ ->
    prerr_endline "usage: forge.ml LOOP.vo";
    exit 2
