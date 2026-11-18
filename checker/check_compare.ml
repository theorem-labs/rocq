(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The comparator of [rocqchk -compare CONFIG -challenge DIR -compare-out FILE].

    The challenge is a set of [.vo] files compiled and checked beforehand,
    and the solution is a tree compiled at the same paths and under the same
    library names. [rocqchk] checks the solution with the kernel as it does
    without the option; this module loads the challenge into a second
    environment without a check, compares every challenge declaration with
    the solution declaration of the same user kernel name, computes each
    named theorem's axiom closure, and writes a JSON verdict.

    The comparison is structural: two declarations are equal when their terms
    are the same after a one-to-one renaming of universe levels, of global
    sort qualities and of functor parameters. There is no conversion and no
    reduction, and no constant is unfolded. Whether the solution may fill a
    constant that the challenge leaves without a body is read from the sort
    of the type the challenge states for it ([stated_sort]), not from that
    type reduced. *)

open Util
open Names
open Declarations

(* clib's [CSha256.file] raises [Sys_error] on a file it cannot read; a
   config that names one is the user's error, reported as such. *)
let sha256_of_file f =
  try CSha256.file f with Sys_error e -> CErrors.user_err (Pp.str e)

(************************************************************************)
(** {6 JSON}

    A reader and a writer of its own. The checker links no JSON reader. The
    one JSON printer it links, [NewProfile.MiniJson] (lib/newProfile.ml),
    copies the bytes above 127 of a string as they are, so a name that is
    not UTF-8 would make the verdict invalid JSON. The writer below escapes
    every such byte and every control character (see [escape]), so any name
    stays one valid JSON string, a line break included. The reader is
    strict, because the config decides the verdict: a duplicate key, a byte
    after the top-level value, a byte sequence that is not UTF-8, a control
    character in a string, a leading zero or a number that is not an
    integer are each an error. *)

module Json = struct

  type t =
    | Null
    | Bool of bool
    | Int of int
    | Str of string
    | List of t list
    | Obj of (string * t) list

  let error msg = CErrors.user_err Pp.(str ("The comparator config is not valid JSON: " ^ msg ^ "."))

  (* The whole input is UTF-8 or the file is refused. *)
  let parse s =
    if not (String.is_valid_utf_8 s) then error "invalid UTF-8";
    let n = String.length s in
    let pos = ref 0 in
    let peek () = if !pos < n then Some s.[!pos] else None in
    let advance () = incr pos in
    let rec skip () =
      match peek () with
      | Some (' ' | '\t' | '\n' | '\r') -> advance (); skip ()
      | _ -> ()
    in
    let expect c =
      match peek () with
      | Some c' when c' = c -> advance ()
      | _ -> error (Printf.sprintf "expected %c at byte %d" c !pos)
    in
    let hex4 () =
      if !pos + 4 > n then error "truncated \\u escape";
      let v = ref 0 in
      for _ = 1 to 4 do
        let c = s.[!pos] in
        let d =
          if c >= '0' && c <= '9' then Char.code c - 48
          else if c >= 'a' && c <= 'f' then Char.code c - 87
          else if c >= 'A' && c <= 'F' then Char.code c - 55
          else error "bad \\u escape"
        in
        v := (!v * 16) + d;
        advance ()
      done;
      !v
    in
    let string_lit () =
      expect '"';
      let b = Buffer.create 32 in
      let rec loop () =
        match peek () with
        | None -> error "unterminated string"
        | Some '"' -> advance (); Buffer.contents b
        | Some '\\' ->
          advance ();
          (match peek () with
           | None -> error "unterminated escape"
           | Some c ->
             advance ();
             (match c with
              | '"' -> Buffer.add_char b '"'
              | '\\' -> Buffer.add_char b '\\'
              | '/' -> Buffer.add_char b '/'
              | 'b' -> Buffer.add_char b '\b'
              | 'f' -> Buffer.add_char b '\012'
              | 'n' -> Buffer.add_char b '\n'
              | 'r' -> Buffer.add_char b '\r'
              | 't' -> Buffer.add_char b '\t'
              | 'u' ->
                let cp = hex4 () in
                let cp =
                  if cp >= 0xd800 && cp <= 0xdbff then begin
                    if !pos + 1 < n && s.[!pos] = '\\' && s.[!pos + 1] = 'u' then begin
                      advance (); advance ();
                      let lo = hex4 () in
                      if lo < 0xdc00 || lo > 0xdfff then error "bad surrogate pair";
                      0x10000 + ((cp - 0xd800) lsl 10) + (lo - 0xdc00)
                    end else error "lone surrogate"
                  end
                  else if cp >= 0xdc00 && cp <= 0xdfff then error "lone surrogate"
                  else cp
                in
                Buffer.add_utf_8_uchar b (Uchar.of_int cp)
              | _ -> error "unknown escape");
             loop ())
        | Some c when Char.code c < 0x20 -> error "control character in a string"
        | Some c -> advance (); Buffer.add_char b c; loop ()
      in
      loop ()
    in
    let number () =
      let start = !pos in
      if peek () = Some '-' then advance ();
      let digits_start = !pos in
      let rec digits () =
        match peek () with
        | Some c when c >= '0' && c <= '9' -> advance (); digits ()
        | _ -> ()
      in
      digits ();
      if !pos = digits_start then error "expected a number";
      if !pos - digits_start > 1 && s.[digits_start] = '0' then error "leading zero in a number";
      (match peek () with
       | Some ('.' | 'e' | 'E') -> error "only integers are accepted"
       | _ -> ());
      let lit = String.sub s start (!pos - start) in
      match int_of_string_opt lit with
      | Some i -> Int i
      | None -> error "the number does not fit"
    in
    let literal lit v =
      if CString.is_sub lit s !pos then (pos := !pos + String.length lit; v)
      else error "unknown literal"
    in
    let rec value () =
      skip ();
      match peek () with
      | None -> error "the file is empty"
      | Some '{' -> obj ()
      | Some '[' -> arr ()
      | Some '"' -> Str (string_lit ())
      | Some 't' -> literal "true" (Bool true)
      | Some 'f' -> literal "false" (Bool false)
      | Some 'n' -> literal "null" Null
      | Some _ -> number ()
    and obj () =
      expect '{';
      skip ();
      if peek () = Some '}' then (advance (); Obj [])
      else
        let rec loop acc =
          skip ();
          let key = string_lit () in
          if List.mem_assoc key acc then error ("the key " ^ key ^ " appears twice");
          skip ();
          expect ':';
          let v = value () in
          let acc = (key, v) :: acc in
          skip ();
          match peek () with
          | Some ',' -> advance (); loop acc
          | Some '}' -> advance (); Obj (List.rev acc)
          | _ -> error "expected , or } in an object"
        in
        loop []
    and arr () =
      expect '[';
      skip ();
      if peek () = Some ']' then (advance (); List [])
      else
        let rec loop acc =
          let v = value () in
          let acc = v :: acc in
          skip ();
          match peek () with
          | Some ',' -> advance (); loop acc
          | Some ']' -> advance (); List (List.rev acc)
          | _ -> error "expected , or ] in an array"
        in
        loop []
    in
    let v = value () in
    skip ();
    if !pos <> n then error "there are bytes after the top-level value";
    v

  let parse_file f =
    let ch = try open_in_bin f with Sys_error e -> CErrors.user_err (Pp.str e) in
    let s =
      Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
          really_input_string ch (in_channel_length ch))
    in
    parse s

  (* The writer. Every character above 127 of a valid UTF-8 sequence is
     written as a \u escape of its code point (a surrogate pair above
     U+FFFF), and each byte that starts no valid sequence as U+FFFD, by the
     reader's rules ([String.get_utf_8_uchar]: no overlong form, no
     surrogate, nothing above U+10FFFF), so the output is valid JSON whatever
     a name holds. *)
  let escape b s =
    let n = String.length s in
    let unicode cp =
      if cp < 0x10000 then Buffer.add_string b (Printf.sprintf "\\u%04x" cp)
      else begin
        let cp = cp - 0x10000 in
        Buffer.add_string b (Printf.sprintf "\\u%04x" (0xd800 lor (cp lsr 10)));
        Buffer.add_string b (Printf.sprintf "\\u%04x" (0xdc00 lor (cp land 0x3ff)))
      end
    in
    let rec loop i =
      if i >= n then ()
      else
        let c = Char.code s.[i] in
        if c = Char.code '"' then (Buffer.add_string b "\\\""; loop (i + 1))
        else if c = Char.code '\\' then (Buffer.add_string b "\\\\"; loop (i + 1))
        else if c = 8 then (Buffer.add_string b "\\b"; loop (i + 1))
        else if c = 12 then (Buffer.add_string b "\\f"; loop (i + 1))
        else if c = 10 then (Buffer.add_string b "\\n"; loop (i + 1))
        else if c = 13 then (Buffer.add_string b "\\r"; loop (i + 1))
        else if c = 9 then (Buffer.add_string b "\\t"; loop (i + 1))
        else if c < 0x20 || c = 0x7f then (unicode c; loop (i + 1))
        else if c < 0x80 then (Buffer.add_char b s.[i]; loop (i + 1))
        else
          let d = String.get_utf_8_uchar s i in
          if Uchar.utf_decode_is_valid d then
            (unicode (Uchar.to_int (Uchar.utf_decode_uchar d));
             loop (i + Uchar.utf_decode_length d))
          else (unicode 0xfffd; loop (i + 1))
    in
    loop 0

  let rec write b = function
    | Null -> Buffer.add_string b "null"
    | Bool true -> Buffer.add_string b "true"
    | Bool false -> Buffer.add_string b "false"
    | Int i -> Buffer.add_string b (string_of_int i)
    | Str s -> Buffer.add_char b '"'; escape b s; Buffer.add_char b '"'
    | List l ->
      Buffer.add_char b '[';
      List.iteri (fun i v -> if i > 0 then Buffer.add_char b ','; write b v) l;
      Buffer.add_char b ']'
    | Obj l ->
      Buffer.add_char b '{';
      List.iteri (fun i (k, v) ->
          if i > 0 then Buffer.add_char b ',';
          Buffer.add_char b '"'; escape b k; Buffer.add_string b "\":";
          write b v) l;
      Buffer.add_char b '}'

  let to_string v = let b = Buffer.create 1024 in write b v; Buffer.contents b
end

(************************************************************************)
(** {6 The config} *)

type theorem = {
  th_name : string;
  th_axioms : string list option;  (** replaces the global list for this one *)
}

type prechecked = { pc_library : DirPath.t; pc_sha256 : string }

type challenge_file = { cf_path : string; cf_sha256 : string }

type config = {
  cfg_theorems : theorem list;
  cfg_axioms : string list;
  cfg_flags : (string * string option) list;
      (** (kind, object): [None] is the kind on any object *)
  cfg_rewrite_rules : bool;
  cfg_prechecked : prechecked list;
  cfg_challenge_files : challenge_file list;
}

(* The kind of the tolerated flag that skips the solution-to-challenge
   universe comparison ([check_constraints]). *)
let universe_constraints_flag = "answer-universe-constraints"

let prechecked_libraries cfg = List.map (fun p -> p.pc_library) cfg.cfg_prechecked

let cfg_error msg = CErrors.user_err Pp.(str ("The comparator config is wrong: " ^ msg ^ "."))

let fields where keys l =
  List.iter (fun (k, _) ->
      if not (List.mem k keys) then
        cfg_error ("the key " ^ k ^ " of " ^ where ^ " is not a key this version knows"))
    l

let get l k = List.assoc_opt k l

let as_string where = function
  | Json.Str s -> s
  | _ -> cfg_error (where ^ " must be a string")

let as_bool where = function
  | Json.Bool b -> b
  | _ -> cfg_error (where ^ " must be true or false")

let as_list where = function
  | Json.List l -> l
  | _ -> cfg_error (where ^ " must be a list")

let as_obj where = function
  | Json.Obj l -> l
  | _ -> cfg_error (where ^ " must be an object")

let string_list where v = List.map (as_string (where ^ "'s entries")) (as_list where v)

(* A pre-checked library is named by its logical name: identifiers separated
   by dots. A name that ends in [.vo], which on the command line names a
   file, is refused rather than read as a library [vo]. *)
let logical_name s =
  let ids = String.split_on_char '.' s in
  if Filename.check_suffix s ".vo" || not (List.for_all Id.is_valid ids) then
    cfg_error ("the prechecked library " ^ s ^ " is not a logical name: identifiers \
                separated by dots, with no .vo");
  DirPath.make (List.rev_map Id.of_string ids)

let read_config file =
  let top = as_obj "the config" (Json.parse_file file) in
  fields "the config"
    ["theorems"; "permitted_axioms"; "tolerated_flags"; "rewrite_rules";
     "prechecked"; "challenge_files"] top;
  let theorems =
    match get top "theorems" with
    | None -> cfg_error "the config has no theorems"
    | Some v ->
      List.map (fun e ->
          let e = as_obj "a theorem" e in
          fields "a theorem" ["name"; "permitted_axioms"] e;
          let name = match get e "name" with
            | None -> cfg_error "a theorem has no name"
            | Some v -> as_string "a theorem's name" v
          in
          { th_name = name;
            th_axioms = Option.map (string_list "a theorem's permitted_axioms")
                (get e "permitted_axioms") })
        (as_list "theorems" v)
  in
  (* A config that names no theorem has no verdict to give, and a name twice
     over would write two records a reader cannot tell apart. *)
  if CList.is_empty theorems then cfg_error "the config names no theorem";
  let rec no_repeat = function
    | [] -> ()
    | th :: tl ->
      if List.exists (fun o -> String.equal o.th_name th.th_name) tl then
        cfg_error ("the theorem " ^ th.th_name ^ " is named twice");
      no_repeat tl
  in
  no_repeat theorems;
  let axioms = match get top "permitted_axioms" with
    | None -> [] | Some v -> string_list "permitted_axioms" v
  in
  (* The rules of [read_config] (check_compare.mli). A kind of
     [never_tolerated] is refused before the object is read, so with an
     object or without; a kind outside [kind_only_allowed] needs an object;
     [universe_constraints_flag] names no declaration and takes none. *)
  let never_tolerated =
    [Check_closure.assumed_positive; Check_closure.unsafe_fixpoint; Check_closure.type_in_type]
  in
  let kind_only_allowed =
    [Check_closure.indices_not_mattering; Check_closure.uip; universe_constraints_flag]
  in
  let flags = match get top "tolerated_flags" with
    | None -> []
    | Some v ->
      List.map (fun e ->
          let e = as_obj "a tolerated flag" e in
          fields "a tolerated flag" ["kind"; "object"] e;
          let k = match get e "kind" with
            | None -> cfg_error "a tolerated flag needs a kind"
            | Some k -> as_string "a tolerated flag's kind" k
          in
          if List.exists (String.equal k) never_tolerated then
            cfg_error ("the tolerated flag " ^ k ^ " is refused with an object or without: " ^
                       "it is a way to prove False whatever the object");
          match get e "object" with
          | Some o ->
            if String.equal k universe_constraints_flag then
              cfg_error ("the tolerated flag " ^ universe_constraints_flag ^
                         " does not name an object");
            k, Some (as_string "a tolerated flag's object" o)
          | None ->
            if not (List.exists (String.equal k) kind_only_allowed) then
              cfg_error ("the tolerated flag " ^ k ^ " needs an object: only " ^
                         Check_closure.indices_not_mattering ^ " and " ^ Check_closure.uip ^
                         " tolerate every object; " ^
                         universe_constraints_flag ^ " is a global check");
            k, None)
        (as_list "tolerated_flags" v)
  in
  let rewrite_rules = match get top "rewrite_rules" with
    | None -> false | Some v -> as_bool "rewrite_rules" v
  in
  let prechecked = match get top "prechecked" with
    | None -> []
    | Some v ->
      List.map (fun e ->
          let e = as_obj "a prechecked entry" e in
          fields "a prechecked entry" ["library"; "sha256"] e;
          match get e "library", get e "sha256" with
          | Some l, Some h ->
            { pc_library = logical_name (as_string "a prechecked library" l);
              pc_sha256 = as_string "a prechecked sha256" h }
          | _ -> cfg_error "a prechecked entry needs a library and a sha256")
        (as_list "prechecked" v)
  in
  let challenge_files = match get top "challenge_files" with
    | None -> cfg_error "the config has no challenge_files"
    | Some v ->
      List.map (fun e ->
          let e = as_obj "a challenge file" e in
          fields "a challenge file" ["path"; "sha256"] e;
          match get e "path", get e "sha256" with
          | Some p, Some h ->
            { cf_path = as_string "a challenge file's path" p;
              cf_sha256 = as_string "a challenge file's sha256" h }
          | _ -> cfg_error "a challenge file needs a path and a sha256")
        (as_list "challenge_files" v)
  in
  if CList.is_empty challenge_files then cfg_error "challenge_files is empty";
  { cfg_theorems = theorems; cfg_axioms = axioms; cfg_flags = flags;
    cfg_rewrite_rules = rewrite_rules; cfg_prechecked = prechecked;
    cfg_challenge_files = challenge_files }

(************************************************************************)
(** {6 The universe level and sort quality maps}

    One map for the whole run, a bijection between the challenge's
    monomorphic levels and the solution's, and another between their global
    sort qualities. A global level, and a global quality that a library
    declares ([Sort s.]), is named by its library and a number given in the
    order of declaration and nothing else, so a solution that declares one
    more before the challenge's numbers them differently. Each map is
    seeded with the identity on every level and quality of a library that
    is one file for both sides, or a library a pre-checked one rests on
    ([seed_umap]), and the rest of it is built while the declarations are
    compared.

    A level or a quality of a polymorphic context is a variable bound by
    position, so it is compared by its index and never enters the map.

    A functor parameter is named by a counter of the process that compiled
    the functor ([MBId.make]), which the two sides need not share either.
    While the signature of a functor is compared, each challenge name under
    one of its parameters is renamed to the solution's parameter of the same
    position before it is compared ([rename]), as the kernel's subtyping
    check renames a functor's parameters. The renaming is applied to each
    name as it is compared, not to the challenge's signature beforehand: a
    substitution of the signature could give the renamed parameter the name
    of a parameter bound inside it, which the other side's process may have
    given that name, and capture its references. *)

type umap = {
  fwd : Univ.Level.t Univ.Level.Map.t;  (** challenge to solution *)
  bwd : Univ.Level.t Univ.Level.Map.t;  (** solution to challenge *)
  qfwd : Sorts.Quality.t Sorts.Quality.Map.t;
      (** challenge to solution, on global qualities ([QGlobal]) only *)
  qbwd : Sorts.Quality.t Sorts.Quality.Map.t;  (** solution to challenge *)
  ties : bool;
      (** whether the constraints of a polymorphic context may decide
          between several solution levels or qualities that fit by taking
          the challenge's own ([map_through_constraints]); only the last
          resort of [compare_declarations] sets it *)
  params : Mod_subst.substitution option;
      (** the challenge's parameters of the functors whose signatures are
          being compared, each to the solution's; [None] outside them *)
  bound : MBId.Set.t;  (** the solution's parameters of those functors *)
}

let empty_umap = {
  fwd = Univ.Level.Map.empty; bwd = Univ.Level.Map.empty;
  qfwd = Sorts.Quality.Map.empty; qbwd = Sorts.Quality.Map.empty;
  ties = false; params = None; bound = MBId.Set.empty;
}

(* The challenge's name [x], with each functor parameter it lies under
   renamed to the solution's ([umap.params]); [f] substitutes a name. *)
let rename m f x = match m.params with
  | None -> x
  | Some s -> f s x

type diff = string

exception Diff of diff

let diff fmt = Printf.ksprintf (fun s -> raise (Diff s)) fmt

(* A universe whose levels no comparison so far has mapped, and that one
   pass cannot map alone (two entries of one increment), or a constraint of
   a polymorphic context on a global level or quality the map does not hold
   yet. The declaration is compared again once the others have been, since
   a later declaration -- the one that introduced those levels -- may map
   them. *)
exception Undecided of diff

let level_name u = Univ.Level.to_string u

let add_level m u v =
  { m with fwd = Univ.Level.Map.add u v m.fwd; bwd = Univ.Level.Map.add v u m.bwd }

let map_level m u v =
  match Univ.Level.var_index u, Univ.Level.var_index v with
  | Some i, Some j ->
    if i <> j then diff "bound universe %s against %s" (level_name u) (level_name v);
    m
  | Some _, None | None, Some _ ->
    diff "universe %s against %s" (level_name u) (level_name v)
  | None, None ->
    match Univ.Level.name u, Univ.Level.name v with
    | None, _ | _, None ->
      (* Set and the other levels with no global name stand for themselves. *)
      if not (Univ.Level.equal u v) then
        diff "universe %s against %s" (level_name u) (level_name v);
      m
    | Some _, Some _ ->
      match Univ.Level.Map.find_opt u m.fwd with
      | Some v' ->
        if not (Univ.Level.equal v v') then
          diff "universe %s is already mapped to %s, not to %s"
            (level_name u) (level_name v') (level_name v);
        m
      | None ->
        match Univ.Level.Map.find_opt v m.bwd with
        | Some u' ->
          diff "universe %s is already mapped from %s, so %s cannot map to it"
            (level_name v) (level_name u') (level_name u)
        | None -> add_level m u v

(* The solution level that the challenge level [u] stands for, when that is
   decided: a level of a polymorphic context, or Set, stands for itself,
   and a global level for the level the map pairs it with. *)
let mapped_level m u =
  match Univ.Level.var_index u, Univ.Level.name u with
  | Some _, _ | None, None -> Some u
  | None, Some _ -> Univ.Level.Map.find_opt u m.fwd

(* A universe is a maximum of levels raised by a constant. Entries whose level
   the map already fixes are matched by that level; the rest are matched by
   their increment, in order. *)
let map_universe m u v =
  let pr_u x = Pp.string_of_ppcmds (Univ.Universe.raw_pr x) in
  let lu = Univ.Universe.repr u and lv = Univ.Universe.repr v in
  if List.length lu <> List.length lv then diff "universe %s against %s" (pr_u u) (pr_u v);
  let m = ref m in
  let rest = ref lv in
  let fresh = ref [] in
  let take_level target n =
    let rec go seen = function
      | [] ->
        diff "universe %s has no %s+%d" (pr_u v) (level_name target) n
      | (l2, n2) :: tl when Univ.Level.equal l2 target && Int.equal n2 n ->
        List.rev_append seen tl
      | e :: tl -> go (e :: seen) tl
    in
    rest := go [] !rest
  in
  List.iter (fun (l, n) ->
      match mapped_level !m l with
      | Some l' -> take_level l' n
      | None -> fresh := (l, n) :: !fresh)
    lu;
  (* What is left on each side is unmapped. Pair only what one pass can
     decide: an entry whose increment is unique among what remains. Each
     pairing can map a level, which may let an earlier entry be matched by
     its level on the next pass, so the passes run until none decides
     anything. Two entries of the same increment and no mapped level are
     ambiguous, and picking by [Universe.repr]'s order would pick
     differently on the two sides, so the comparison stops instead. *)
  let fresh = ref (List.rev !fresh) in
  let rec passes () =
    if CList.is_empty !fresh then ()
    else begin
      if not (List.length !fresh = List.length !rest) then
        diff "universe %s against %s" (pr_u u) (pr_u v);
      let decided = ref false in
      let keep = ref [] in
      List.iter (fun (l, n) ->
          match Univ.Level.Map.find_opt l !m.fwd with
          | Some l' ->
            (* mapped since this entry was set aside: match it by level *)
            take_level l' n;
            decided := true
          | None ->
            match List.filter (fun (_, n2) -> Int.equal n n2) !rest with
            | [ (l2, _) ] ->
              m := map_level !m l l2;
              take_level l2 n;
              decided := true
            | [] ->
              diff "universe %s has no entry of increment %d" (pr_u v) n
            | _ :: _ :: _ -> keep := (l, n) :: !keep)
        !fresh;
      let left = List.rev !keep in
      if not !decided then
        raise (Undecided (Printf.sprintf
          "universe %s against %s: which level of the solution each level of the \
           challenge stands for is not decided"
          (pr_u u) (pr_u v)));
      fresh := left;
      passes ()
    end
  in
  passes ();
  !m

let quality_name = function
  | Sorts.Quality.QConstant c -> Pp.string_of_ppcmds (Sorts.Quality.Constants.pr c)
  | Sorts.Quality.QGlobal q -> Sorts.QGlobal.to_string q
  | Sorts.Quality.QVar q -> Sorts.QVar.to_string q

let add_quality m q1 q2 =
  { m with qfwd = Sorts.Quality.Map.add q1 q2 m.qfwd;
           qbwd = Sorts.Quality.Map.add q2 q1 m.qbwd }

(* A global quality maps to a global quality, one-to-one, as [map_level]
   maps a global level. A constant ([SProp], [Prop], [Type]) stands for
   itself, and so does a quality variable of a polymorphic context, bound by
   position. *)
let map_quality m q1 q2 =
  let open Sorts.Quality in
  match q1, q2 with
  | QGlobal _, QGlobal _ ->
    (match Map.find_opt q1 m.qfwd with
     | Some q' ->
       if not (equal q2 q') then
         diff "sort quality %s is already mapped to %s, not to %s"
           (quality_name q1) (quality_name q') (quality_name q2);
       m
     | None ->
       match Map.find_opt q2 m.qbwd with
       | Some q' ->
         diff "sort quality %s is already mapped from %s, so %s cannot map to it"
           (quality_name q2) (quality_name q') (quality_name q1)
       | None -> add_quality m q1 q2)
  | (QConstant _ | QVar _), _ | QGlobal _, (QConstant _ | QVar _) ->
    if not (equal q1 q2) then
      diff "sort quality %s against %s" (quality_name q1) (quality_name q2);
    m

(* The solution quality that the challenge quality [q] stands for, when
   that is decided, as [mapped_level] gives it for a level. *)
let mapped_quality m q = match q with
  | Sorts.Quality.QGlobal _ -> Sorts.Quality.Map.find_opt q m.qfwd
  | Sorts.Quality.QConstant _ | Sorts.Quality.QVar _ -> Some q

(* A sort is compared by its quality and its universe. The quality of a
   [GSort] is a global quality, which goes through the quality map, as its
   universe and the universe of [Type] go through the level map. *)
let map_sort m s1 s2 =
  let open Sorts in
  match s1, s2 with
  | SProp, SProp | Prop, Prop | Set, Set -> m
  | Type u, Type v -> map_universe m u v
  | GSort (q1, u), GSort (q2, v) ->
    map_universe (map_quality m (Quality.QGlobal q1) (Quality.QGlobal q2)) u v
  | VSort (q1, u), VSort (q2, v) ->
    if not (QVar.equal q1 q2) then diff "sort variable";
    map_universe m u v
  | (SProp | Prop | Set | Type _ | GSort _ | VSort _), _ -> diff "sort"

let map_instance m i1 i2 =
  let q1, u1 = UVars.Instance.to_array i1 and q2, u2 = UVars.Instance.to_array i2 in
  if Array.length q1 <> Array.length q2 || Array.length u1 <> Array.length u2 then
    diff "universe instance";
  let m = Array.fold_left2 map_quality m q1 q2 in
  Array.fold_left2 map_level m u1 u2

let map_relevance r1 r2 =
  if not (Sorts.relevance_equal r1 r2) then diff "relevance"

let map_annot a1 a2 =
  map_relevance a1.Context.binder_relevance a2.Context.binder_relevance

(************************************************************************)
(** {6 Structural equality of terms}

    No conversion, no reduction, and no constant is unfolded: two terms are
    equal when they have the same shape, the same kernel names (a
    challenge's name renamed under functor parameters, [rename]) and
    universes the map pairs. Binder names are not compared, their relevance
    is. A [Cast] is a type ascription the kernel has already used, so it is
    stripped on both sides. *)

let rec eq_constr m c1 c2 =
  let open Constr in
  match kind c1, kind c2 with
  | Cast (c1, _, _), _ -> eq_constr m c1 c2
  | _, Cast (c2, _, _) -> eq_constr m c1 c2
  | Rel i, Rel j -> if not (Int.equal i j) then diff "de Bruijn index"; m
  | Var i, Var j -> if not (Id.equal i j) then diff "section variable"; m
  | Meta _, _ | _, Meta _ -> diff "a term holds a metavariable"
  | Evar _, _ | _, Evar _ -> diff "a term holds an existential variable"
  | Sort s1, Sort s2 -> map_sort m s1 s2
  | Prod (a1, t1, b1), Prod (a2, t2, b2) ->
    map_annot a1 a2; eq_constr (eq_constr m t1 t2) b1 b2
  | Lambda (a1, t1, b1), Lambda (a2, t2, b2) ->
    map_annot a1 a2; eq_constr (eq_constr m t1 t2) b1 b2
  | LetIn (a1, v1, t1, b1), LetIn (a2, v2, t2, b2) ->
    map_annot a1 a2; eq_constr (eq_constr (eq_constr m v1 v2) t1 t2) b1 b2
  | App (f1, a1), App (f2, a2) ->
    if not (Int.equal (Array.length a1) (Array.length a2)) then diff "number of arguments";
    Array.fold_left2 eq_constr (eq_constr m f1 f2) a1 a2
  | Const (c1, u1), Const (c2, u2) ->
    let c1 = rename m Mod_subst.subst_constant c1 in
    if not (Constant.CanOrd.equal c1 c2) then
      diff "constant %s against %s" (Constant.to_string c1) (Constant.to_string c2);
    map_instance m u1 u2
  | Ind ((i1, n1), u1), Ind ((i2, n2), u2) ->
    let i1 = rename m Mod_subst.subst_mind i1 in
    if not (MutInd.CanOrd.equal i1 i2 && Int.equal n1 n2) then
      diff "inductive %s against %s" (MutInd.to_string i1) (MutInd.to_string i2);
    map_instance m u1 u2
  | Construct (((i1, n1), k1), u1), Construct (((i2, n2), k2), u2) ->
    let i1 = rename m Mod_subst.subst_mind i1 in
    if not (MutInd.CanOrd.equal i1 i2 && Int.equal n1 n2 && Int.equal k1 k2) then
      diff "constructor of %s against %s" (MutInd.to_string i1) (MutInd.to_string i2);
    map_instance m u1 u2
  | Case (ci1, u1, pms1, p1, iv1, s1, br1), Case (ci2, u2, pms2, p2, iv2, s2, br2) ->
    let (m1, n1) = ci1.ci_ind and (m2, n2) = ci2.ci_ind in
    let m1 = rename m Mod_subst.subst_mind m1 in
    if not (MutInd.CanOrd.equal m1 m2 && Int.equal n1 n2) then diff "match on another inductive";
    if not (Int.equal ci1.ci_npar ci2.ci_npar) then diff "match parameters";
    let m = map_instance m u1 u2 in
    if not (Int.equal (Array.length pms1) (Array.length pms2)) then diff "match parameters";
    let m = Array.fold_left2 eq_constr m pms1 pms2 in
    let ((nas1, t1), r1) = p1 and ((nas2, t2), r2) = p2 in
    if not (Int.equal (Array.length nas1) (Array.length nas2)) then diff "match return clause";
    Array.iter2 map_annot nas1 nas2;
    map_relevance r1 r2;
    let m = eq_constr m t1 t2 in
    let m = match iv1, iv2 with
      | NoInvert, NoInvert -> m
      | CaseInvert { indices = a1 }, CaseInvert { indices = a2 } ->
        if not (Int.equal (Array.length a1) (Array.length a2)) then diff "match indices";
        Array.fold_left2 eq_constr m a1 a2
      | (NoInvert | CaseInvert _), _ -> diff "match inversion"
    in
    let m = eq_constr m s1 s2 in
    if not (Int.equal (Array.length br1) (Array.length br2)) then diff "number of branches";
    Array.fold_left2 (fun m (nas1, b1) (nas2, b2) ->
        if not (Int.equal (Array.length nas1) (Array.length nas2)) then diff "branch binders";
        Array.iter2 map_annot nas1 nas2;
        eq_constr m b1 b2)
      m br1 br2
  | Fix ((ln1, i1), (nas1, tl1, bl1)), Fix ((ln2, i2), (nas2, tl2, bl2)) ->
    if not (Array.equal Int.equal ln1 ln2 && Int.equal i1 i2) then diff "fixpoint structure";
    eq_recdecl m (nas1, tl1, bl1) (nas2, tl2, bl2)
  | CoFix (i1, (nas1, tl1, bl1)), CoFix (i2, (nas2, tl2, bl2)) ->
    if not (Int.equal i1 i2) then diff "cofixpoint structure";
    eq_recdecl m (nas1, tl1, bl1) (nas2, tl2, bl2)
  | Proj (p1, r1, c1), Proj (p2, r2, c2) ->
    let p1 = rename m Mod_subst.subst_proj p1 in
    if not (Projection.CanOrd.equal p1 p2) then
      diff "projection %s against %s" (Projection.to_string p1) (Projection.to_string p2);
    map_relevance r1 r2;
    eq_constr m c1 c2
  | Int i, Int j -> if not (Uint63.equal i j) then diff "integer literal"; m
  | Float f, Float g -> if not (Float64.equal f g) then diff "float literal"; m
  | String s, String t -> if not (Pstring.equal s t) then diff "string literal"; m
  | Array (u1, v1, d1, t1), Array (u2, v2, d2, t2) ->
    if not (Int.equal (Array.length v1) (Array.length v2)) then diff "array length";
    let m = map_instance m u1 u2 in
    let m = Array.fold_left2 eq_constr m v1 v2 in
    eq_constr (eq_constr m d1 d2) t1 t2
  | (Rel _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _ | Const _
    | Ind _ | Construct _ | Case _ | Fix _ | CoFix _ | Proj _ | Int _ | Float _
    | String _ | Array _), _ -> diff "the terms have different shapes"

and eq_recdecl m (nas1, tl1, bl1) (nas2, tl2, bl2) =
  if not (Int.equal (Array.length tl1) (Array.length tl2)) then diff "recursive block size";
  Array.iter2 map_annot nas1 nas2;
  let m = Array.fold_left2 eq_constr m tl1 tl2 in
  Array.fold_left2 eq_constr m bl1 bl2

(************************************************************************)
(** {6 Declarations}

    Every field of [constant_body], [mutual_inductive_body],
    [one_inductive_body], [typing_flags] and [machine_rewrite_rule] is named
    below, in the pattern that reads it: compared, or bound to [_] with the
    reason beside it. Each of those patterns turns warning 9 (a record
    pattern that leaves a field out) back on, so a field the kernel adds
    breaks the build here instead of going uncompared. *)

let eq_rel_context m c1 c2 =
  let open Context.Rel.Declaration in
  if not (Int.equal (List.length c1) (List.length c2)) then diff "context length";
  List.fold_left2 (fun m d1 d2 ->
      match d1, d2 with
      | LocalAssum (a1, t1), LocalAssum (a2, t2) -> map_annot a1 a2; eq_constr m t1 t2
      | LocalDef (a1, b1, t1), LocalDef (a2, b2, t2) ->
        map_annot a1 a2; eq_constr (eq_constr m b1 b2) t1 t2
      | (LocalAssum _ | LocalDef _), _ -> diff "a let-in of the context")
    m c1 c2

(* A global level or quality that only the constraints of a polymorphic
   context name is mapped by them. For a challenge constraint [(x, k, u)]
   whose [x] stands for [x'] and whose [u] the map does not hold, the
   solution must hold [(x', k, v)] for the [v] that [u] stands for, and [v]
   can only be a global one that nothing maps to yet ([free]). When exactly
   one solution constraint has that shape, [u] maps to its [v] ([add] keeps
   the map one-to-one), and the same holds the other way round for
   [(u, k, x)]. Each such mapping can decide another constraint, so the
   passes run until one maps nothing; what is still unmapped then is the
   caller's to report.

   When several solution constraints have that shape, none of them is
   taken, unless [m.ties] is set and one of them is [u] itself: the same
   library and number, which the two sides share when the solution declares
   [u] where the challenge does. Any pairing is sound, since everything
   compared after it -- the rest of the context, the other declarations and
   both graphs -- is compared through the map it leaves, so a wrong one can
   only fail a solution. [compare_declarations] sets [m.ties] only once
   nothing else decides, so a comparison that maps [u] by a term comes
   first.

   The universe constraints and the elimination constraints of a context
   have the same shape: [mapped] reads a challenge end through the map,
   [free] tells whether a solution end may still be mapped to, [same] and
   [same_kind] compare ends and kinds, and [add] maps an end. *)
let map_through_constraints ~mapped ~free ~same ~same_kind ~add m challenge solution =
  (* The end that the unmapped end [u] may map to: [ends] reads a solution
     constraint as its end opposite [u]'s place, then its end at [u]'s
     place. *)
  let target m k x' u ends =
    let fits ((_, k2, _) as c) =
      let x2, v = ends c in
      if same_kind k k2 && same x2 x' && free m v then Some v else None
    in
    match List.filter_map fits solution with
    | [ v ] -> Some v
    | [] -> None
    | _ :: _ :: _ as l -> if m.ties && List.exists (same u) l then Some u else None
  in
  let step (m, rest) ((u, k, v) as c) =
    match mapped m u, mapped m v with
    | Some _, Some _ -> m, rest
    | Some u', None ->
      (match target m k u' v (fun (a, _, b) -> a, b) with
       | Some v' -> add m v v', rest
       | None -> m, c :: rest)
    | None, Some v' ->
      (match target m k v' u (fun (a, _, b) -> b, a) with
       | Some u' -> add m u u', rest
       | None -> m, c :: rest)
    | None, None -> m, c :: rest
  in
  let rec passes m pending =
    let m, rest = List.fold_left step (m, []) pending in
    if List.length rest < List.length pending then passes m (List.rev rest) else m
  in
  passes m challenge

(* The universe constraints [c1] and [c2] of two polymorphic contexts. A
   constraint may relate a bound level to a global one, which the two sides
   may number differently, so a global level of the challenge's is compared
   as the solution level the map pairs it with, as everywhere else. That is
   why this runs once the rest of the declaration has been compared: its
   terms may map the level. The map is one-to-one, so it maps [c1] to a set
   of the same size: two sets of different sizes differ whatever it maps,
   which is reported before any level is mapped. A global level that only
   the constraints name is mapped by them ([map_through_constraints]); one
   still unmapped then, which no such constraint or several fit, leaves the
   declaration undecided, as an ambiguous universe does in
   [map_universe]. *)
let eq_context_constraints m c1 c2 =
  let size = Univ.UnivConstraints.cardinal in
  if not (Int.equal (size c1) (size c2)) then
    diff "the universe context has other constraints";
  let m =
    map_through_constraints ~mapped:mapped_level
      ~free:(fun m v -> Option.has_some (Univ.Level.name v) && not (Univ.Level.Map.mem v m.bwd))
      ~same:Univ.Level.equal
      ~same_kind:(fun k k2 -> Int.equal (Univ.UnivConstraint.compare_kind k k2) 0)
      ~add:map_level m (Univ.UnivConstraints.elements c1) (Univ.UnivConstraints.elements c2)
  in
  let level u = match mapped_level m u with
    | Some v -> v
    | None ->
      raise (Undecided (Printf.sprintf
        "the universe context constrains the universe %s, which no comparison has mapped"
        (level_name u)))
  in
  let c1 =
    Univ.UnivConstraints.fold (fun (u, k, v) acc ->
        Univ.UnivConstraints.add (level u, k, level v) acc)
      c1 Univ.UnivConstraints.empty
  in
  if not (Univ.UnivConstraints.equal c1 c2) then
    diff "the universe context has other constraints";
  m

(* The elimination constraints [e1] and [e2] of two polymorphic contexts,
   compared as [eq_context_constraints] compares their universe constraints:
   a constraint may relate a bound quality to a global one, which goes
   through the quality map, and a global quality that only the constraints
   name is mapped by them. *)
let eq_elim_context_constraints m e1 e2 =
  let module EC = Sorts.ElimConstraints in
  if not (Int.equal (EC.cardinal e1) (EC.cardinal e2)) then
    diff "the universe context has other constraints";
  let same_kind k k2 = match k, k2 with
    | Sorts.ElimConstraint.ElimTo, Sorts.ElimConstraint.ElimTo -> true
  in
  let m =
    map_through_constraints ~mapped:mapped_quality
      ~free:(fun m q -> Sorts.Quality.is_qglobal q && not (Sorts.Quality.Map.mem q m.qbwd))
      ~same:Sorts.Quality.equal ~same_kind ~add:map_quality m (EC.elements e1) (EC.elements e2)
  in
  let quality q = match mapped_quality m q with
    | Some q' -> q'
    | None ->
      raise (Undecided (Printf.sprintf
        "the universe context constrains the sort quality %s, which no comparison has mapped"
        (quality_name q)))
  in
  let e1 = EC.fold (fun (q1, k, q2) acc -> EC.add (quality q1, k, quality q2) acc) e1 EC.empty in
  if not (EC.equal e1 e2) then diff "the universe context has other constraints";
  m

(* Two abstract universe contexts of one size. Returns the comparison of
   their elimination and universe constraints ([eq_elim_context_constraints],
   [eq_context_constraints]), for the caller to run once the rest of the
   declaration has been compared. *)
let eq_abstract_context a1 a2 =
  if UVars.AbstractContext.size a1 <> UVars.AbstractContext.size a2 then
    diff "the universe context has another size";
  let (e1, c1) = UVars.UContext.constraints (UVars.AbstractContext.repr a1) in
  let (e2, c2) = UVars.UContext.constraints (UVars.AbstractContext.repr a2) in
  fun m -> eq_context_constraints (eq_elim_context_constraints m e1 e2) c1 c2

(* The shape of two universe contexts: both monomorphic, or both
   polymorphic ([eq_abstract_context]). *)
let eq_universes u1 u2 = match u1, u2 with
  | Monomorphic, Monomorphic -> fun m -> m
  | Polymorphic a1, Polymorphic a2 -> eq_abstract_context a1 a2
  | Monomorphic, Polymorphic _ -> diff "a monomorphic declaration is polymorphic in the solution"
  | Polymorphic _, Monomorphic -> diff "a polymorphic declaration is monomorphic in the solution"

(* What the challenge leaves without a body, the solution may fill only when
   the challenge states it as a proposition or the config names it as a
   theorem. [Admitted], [Axiom] and [Parameter] give the same .vo content,
   so the kind of the declaration cannot tell them apart; its type can.
   Proving a lemma is the point. A constant of any other type -- an open
   definition -- must stay without a body, or the solution could choose the
   function the statements are about, unless the config names it: the
   challenge then asks the solution to choose it, as for a function [f]
   left open with a lemma [f_spec] about it.

   A constant that another compared challenge declaration names in its type
   or its transparent body ([named], from [declaration_names]) must be
   opaque, whether the config names it or not, unless the challenge states
   it as data. The challenge states that declaration about a constant that
   does not unfold, and a transparent body would let conversion unfold it
   there, which changes what the declaration states: with
   [L : exists n, n = 0] left without a body, [L = ex_intro _ 0 eq_refl] is
   not provable, and once [L] is defined as that term it is proved by
   reflexivity. A constant that no other declaration names changes no
   statement but its own, so it may be transparent. A function
   [f : nat -> nat] that the config names is not held to this: [f_spec] is
   stated about the function the solution chooses and is provable only if
   [f] unfolds.

   Both rules read only what the challenge's author wrote: the sort of the
   type the challenge states for the constant ([stated_sort]). In [Prop] or
   [SProp], the constant is a proposition. In [Set] or [Type], it is data,
   even when its type unfolds to a proposition: with
   [Spec : Type := exists n, n = 0], [L : Spec] is data, which the solution
   may define transparently when the config names it, so a challenge that
   wants a lemma kept opaque states it in [Prop]. In a sort variable or a
   global sort, or when the type cannot be typed, the run cannot tell, and
   each rule takes its refusing side: a sort-polymorphic constant is a
   proof at an instance in [Prop], and a global sort, which a library
   declares, may be meant for propositions. *)
type sort_class = Proposition | Data | Undetermined

(* The class of the sort of the type that the challenge states for its
   constant [cb]: the principal sort of that type in [env], the challenge
   environment, under the constant's own typing flags and universe context,
   as the kernel check types a constant (mod_checking.ml). The type is not
   reduced, and the challenge environment holds no declaration of the
   solution's, so no body the solution chose is unfolded. [Undetermined]
   for a sort variable or a global sort, for a type that cannot be typed
   there, and without an environment: a field of a module type, whose type
   may name the other fields of the module type and the functor parameters,
   which no environment holds. *)
let stated_sort env (cb : constant_body) =
  match env with
  | None -> Undetermined
  | Some env ->
    let env = CheckFlags.set_local_flags cb.const_typing_flags env in
    let env = match cb.const_universes with
      | Monomorphic -> env
      | Polymorphic ctx ->
        Environ.push_context ~strict:false (UVars.AbstractContext.repr ctx) env
    in
    match (Typeops.infer_type env cb.const_type).Environ.utj_type with
    | Sorts.Prop | Sorts.SProp -> Proposition
    | Sorts.Set | Sorts.Type _ -> Data
    | Sorts.GSort _ | Sorts.VSort _ -> Undetermined
    | exception e when CErrors.noncritical e -> Undetermined

(* [env]: the challenge environment that [stated_sort] reads, [None] for a
   field of a module type. *)
let eq_const_body ~env ~is_theorem ~named m (cb1 : constant_body) (cb2 : constant_body) =
  let[@warning "+9"] {
    const_relevance; const_universes; const_type; const_body;
    const_hyps = _;
    (* empty: discharge removes each section's variables as the section
       closes, and a compiled library has no section open *)
    const_univ_hyps = _;
    (* empty, for the same reason *)
    const_body_code = _;
    (* the bytecode compiled from the body *)
    const_inline_code = _;
    (* whether the compilers inline the constant: how it runs, not what it
       states *)
    const_typing_flags = _;
    (* the checker types each solution constant under the checker's
       [indices_matter], [impredicative_set] and [sprop_allowed], not the
       constant's ([CheckFlags.set_local_flags] keeps the environment's);
       the relaxed conditions the constant may carry reach the verdict as
       the closure's flags; the rest steer how conversion computes *)
    const_def_height = _;
    (* derived from the body, for the unfolding heuristic of conversion *)
  } = cb1
  in
  map_relevance const_relevance cb2.const_relevance;
  let context_constraints = eq_universes const_universes cb2.const_universes in
  let m = eq_constr m const_type cb2.const_type in
  (* forced only by a constant the challenge leaves without a body and the
     solution fills *)
  let sort = lazy (stated_sort env cb1) in
  let m = match const_body, cb2.const_body with
    | Undef _, Undef _ -> m
    | Undef _, (Def _ | OpaqueDef _)
      when not is_theorem
           && (match Lazy.force sort with Proposition -> false | Data | Undetermined -> true) ->
      diff "the challenge leaves this declaration open and the solution defines it"
    | Undef _, Def _
      when (match Lazy.force sort with Data -> false | Proposition | Undetermined -> true)
           && Lazy.force named ->
      diff "the challenge leaves this constant without a body, another challenge \
            declaration names it, and the solution gives it a transparent body"
    | Undef _, (Def _ | OpaqueDef _) -> m
    | Undef _, _ -> diff "an assumption is a primitive or a symbol in the solution"
    (* An opaque body is never compared, but a proof stays a proof: a Qed in
       the challenge may not become a transparent definition, which would let
       the solution's body reach conversion where the challenge's could not. *)
    | OpaqueDef _, OpaqueDef _ -> m
    | Def b1, Def b2 -> eq_constr m b1 b2
    | Def _, OpaqueDef _ -> diff "a transparent definition is opaque in the solution"
    | Def _, _ -> diff "a transparent definition is not a definition in the solution"
    | OpaqueDef _, _ -> diff "an opaque proof is not an opaque proof in the solution"
    | Primitive p1, Primitive p2 ->
      if not (CPrimitives.equal p1 p2) then diff "another primitive"; m
    | Primitive _, _ -> diff "a primitive is not a primitive in the solution"
    (* A symbol's [unfold_fix] flag steers only the matching of its rules,
       which reach the verdict through the config's [rewrite_rules]. *)
    | Symbol _, Symbol _ -> m
    | Symbol _, _ -> diff "a symbol is not a symbol in the solution"
  in
  context_constraints m

let eq_has_eta e1 e2 = match e1, e2 with
  | AlwaysEta, AlwaysEta | MaybeEta, MaybeEta | NoEta, NoEta -> true
  | (AlwaysEta | MaybeEta | NoEta), _ -> false

let[@warning "+9"] eq_record m r1 r2 = match r1, r2 with
  | NotRecord, NotRecord | FakeRecord, FakeRecord -> m
  | PrimRecord { id; projections; relevances; tys; has_eta }, PrimRecord p2 ->
    if not (Id.equal id p2.id) then diff "the record binder name";
    if not (Array.equal Id.equal projections p2.projections) then diff "the projections";
    if not (Array.equal Sorts.relevance_equal relevances p2.relevances) then
      diff "a projection's relevance";
    if not (eq_has_eta has_eta p2.has_eta) then diff "the record's eta";
    if not (Int.equal (Array.length tys) (Array.length p2.tys)) then diff "the projections";
    Array.fold_left2 eq_constr m tys p2.tys
  | (NotRecord | FakeRecord | PrimRecord _), _ -> diff "the record kind"

let eq_variance v1 v2 =
  if not (Option.equal (Array.equal UVars.Variance.equal) v1 v2) then
    diff "the universe variance"

(* The relaxed kernel conditions a declaration was typed under are part of
   what it claims. The conversion oracle and the performance switches are
   not: they change how the kernel works, not what it accepted. *)
let eq_typing_flags (f1 : typing_flags) (f2 : typing_flags) =
  let[@warning "+9"] {
    check_guarded; check_positive; check_universes; check_eliminations;
    indices_matter; impredicative_set;
    conv_oracle = _;
    (* the order in which conversion unfolds constants *)
    share_reduction = _;
    (* a reduction strategy *)
    unfold_dep_heuristic = _;
    (* a heuristic of conversion *)
    unfold_height_heuristic = _;
    (* a heuristic of conversion *)
    enable_VM = _;
    (* whether VM conversion falls back to the interpreted one *)
    enable_native_compiler = _;
    (* whether native conversion falls back to the VM *)
    sprop_allowed = _;
    (* whether a term may hold SProp, which the compared terms show *)
    allow_uip = _;
    (* a block that uses definitional UIP is not squashed ([mind_squashed],
       compared) and reaches the verdict as the closure's [uip] flag *)
  } = f1
  in
  if check_guarded <> f2.check_guarded
  || check_positive <> f2.check_positive
  || check_universes <> f2.check_universes
  || check_eliminations <> f2.check_eliminations
  || indices_matter <> f2.indices_matter
  || impredicative_set <> f2.impredicative_set
  then diff "the kernel conditions the declaration was typed under"

(* The qualities at which a block is squashed: the challenge's are compared
   through the quality map. *)
let eq_squashed m s1 s2 = match s1, s2 with
  | None, None | Some AlwaysSquashed, Some AlwaysSquashed -> ()
  | Some (SometimesSquashed q1), Some (SometimesSquashed q2) ->
    let mapped q = match mapped_quality m q with
      | Some q' -> q'
      | None ->
        raise (Undecided (Printf.sprintf
          "the elimination restriction names the sort quality %s, which no comparison has \
           mapped"
          (quality_name q)))
    in
    if not (Sorts.Quality.Set.equal (Sorts.Quality.Set.map mapped q1) q2) then
      diff "the elimination restriction"
  | (None | Some (AlwaysSquashed | SometimesSquashed _)), _ -> diff "the elimination restriction"

let eq_one_ind m (mip1 : one_inductive_body) (mip2 : one_inductive_body) =
  let[@warning "+9"] {
    mind_typename; mind_relevance; mind_arity_ctxt; mind_user_arity; mind_sort;
    mind_nrealargs; mind_squashed; mind_consnames; mind_user_lc; mind_record;
    mind_nrealdecls = _;
    (* the length of [mind_arity_ctxt] without the parameters *)
    mind_nf_lc = _;
    (* derived from [mind_user_lc] by reduction, through the constants it
       unfolds, which are compared on their own or are one file for both
       sides *)
    mind_consnrealargs = _;
    (* derived from [mind_nf_lc] *)
    mind_consnrealdecls = _;
    (* derived from [mind_nf_lc] *)
    mind_automaton = _;
    (* the recursive arguments, which the kernel computes from the
       constructor types *)
    mind_relies_on_indices_not_mattering = _;
    (* computed from the universe graph when the block is typed, and
       reaches the verdict as the closure's [indices-not-mattering] flag *)
    mind_nb_constant = _;
    (* VM data, derived from the constructors *)
    mind_nb_args = _;
    (* VM data, derived from the constructors *)
    mind_reloc_tbl = _;
    (* VM data, derived from the constructors *)
  } = mip1
  in
  if not (Id.equal mind_typename mip2.mind_typename) then diff "the type's name";
  map_relevance mind_relevance mip2.mind_relevance;
  let m = eq_rel_context m mind_arity_ctxt mip2.mind_arity_ctxt in
  let m = eq_constr m mind_user_arity mip2.mind_user_arity in
  let m = map_sort m mind_sort mip2.mind_sort in
  if not (Int.equal mind_nrealargs mip2.mind_nrealargs) then diff "the number of indices";
  if not (Array.equal Id.equal mind_consnames mip2.mind_consnames) then
    diff "the constructor names";
  if not (Int.equal (Array.length mind_user_lc) (Array.length mip2.mind_user_lc)) then
    diff "the number of constructors";
  let m = Array.fold_left2 eq_constr m mind_user_lc mip2.mind_user_lc in
  (* after the constructors, whose types may map the qualities it names *)
  eq_squashed m mind_squashed mip2.mind_squashed;
  eq_record m mind_record mip2.mind_record

(* The template data of two template-polymorphic blocks. The other fields
   of a block are typed over the levels that the template context binds,
   which they name by index, and the kernel instantiates them with the
   default levels ([template_defaults]) where it reads them
   ([Inductive.get_template_instance]); [eq_mib_body] compares them with
   their bound levels by index. An application of the block is typed by
   this data: which parameters bind a level or a quality
   ([template_param_arguments]), the sort of the block in terms of them
   ([template_concl]), and the context they are bound in
   ([template_context]). No other field names the defaults. So the data is
   compared as a polymorphic declaration is: the sorts with their bound
   levels by index, the defaults through the level map, and the context by
   [eq_abstract_context]. Which parameters bind something is compared at
   once; the rest is returned for the caller to run once the rest of the
   block has been compared. *)
let[@warning "+9"] eq_template
    { template_param_arguments; template_concl; template_context; template_defaults } t2 =
  if not (CList.equal (fun a b -> Bool.equal (Option.has_some a) (Option.has_some b))
            template_param_arguments t2.template_param_arguments)
  then diff "the template-polymorphic parameters";
  let context_constraints = eq_abstract_context template_context t2.template_context in
  fun m ->
    let m = List.fold_left2 (fun m a1 a2 -> match a1, a2 with
        | Some s1, Some s2 -> map_sort m s1 s2
        | None, None -> m
        | (None | Some _), _ -> diff "the template-polymorphic parameters")
        m template_param_arguments t2.template_param_arguments
    in
    let m = map_sort m template_concl t2.template_concl in
    context_constraints (map_instance m template_defaults t2.template_defaults)

let eq_mib_body m (mib1 : mutual_inductive_body) (mib2 : mutual_inductive_body) =
  let[@warning "+9"] {
    mind_finite; mind_nparams; mind_nparams_rec; mind_private; mind_template;
    mind_typing_flags; mind_variance; mind_sec_variance; mind_universes;
    mind_params_ctxt; mind_packets;
    mind_hyps = _;
    (* empty: discharge removes each section's variables as the section
       closes, and a compiled library has no section open *)
    mind_univ_hyps = _;
    (* empty, for the same reason *)
  } = mib1
  in
  if mind_finite <> mib2.mind_finite then diff "the recursivity kind";
  if not (Int.equal mind_nparams mib2.mind_nparams) then diff "the number of parameters";
  if not (Int.equal mind_nparams_rec mib2.mind_nparams_rec) then
    diff "the number of uniform parameters";
  if mind_private <> mib2.mind_private then diff "the private flag";
  let template_data = match mind_template, mib2.mind_template with
    | None, None -> fun m -> m
    | Some t1, Some t2 -> eq_template t1 t2
    | (None | Some _), _ ->
      diff "a template-polymorphic inductive type is not template-polymorphic in the solution"
  in
  eq_typing_flags mind_typing_flags mib2.mind_typing_flags;
  eq_variance mind_variance mib2.mind_variance;
  eq_variance mind_sec_variance mib2.mind_sec_variance;
  let context_constraints = eq_universes mind_universes mib2.mind_universes in
  let m = eq_rel_context m mind_params_ctxt mib2.mind_params_ctxt in
  if not (Int.equal (Array.length mind_packets) (Array.length mib2.mind_packets)) then
    diff "the number of types in the block";
  let m = Array.fold_left2 eq_one_ind m mind_packets mib2.mind_packets in
  context_constraints (template_data m)

(* The symbols a block of rewrite rules rewrites, in order. That is all of a
   rule the comparison reads: a rule reaches the verdict through the
   config's [rewrite_rules], without which every theorem fails on the first
   rule a library of the solution declares. *)
let[@warning "+9"] rule_symbols { rewrules_rules } =
  List.map (fun (symbol, {
      nvars = _;
      (* the number of pattern variables *)
      lhs_pat = _;
      (* the pattern *)
      rhs = _;
      (* the replacement *)
      test = _;
      (* the terms the kernel converts when a definition implements a
         symbol of a signature *)
    }) -> symbol)
    rewrules_rules

(* [declaration_names]: the kernel names of the constants that compared
   challenge declarations name in what the comparison reads of them -- a
   constant's type and transparent body, a block's parameters, arities,
   constructor types and projection types, and every field of a module
   type, the types of its functor parameters included -- each under its
   user name and its canonical one, so a reference through an alias
   counts. An opaque body is not read: it is not compared, and what it
   names unfolds into no statement. Nor is a rewrite rule, of which the
   comparison reads the symbols only. When the challenge leaves a constant
   that this set holds without a body, [eq_const_body] requires the
   solution's to be opaque unless the challenge states it as data. *)
let rec constr_names acc c = match Constr.kind c with
  | Constr.Const (k, _) ->
    KerName.Set.add (Constant.user k) (KerName.Set.add (Constant.canonical k) acc)
  | _ -> Constr.fold constr_names acc c

let const_names acc (cb : constant_body) =
  let acc = constr_names acc cb.const_type in
  match cb.const_body with
  | Def b -> constr_names acc b
  | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> acc

let mind_names acc (mib : mutual_inductive_body) =
  let context acc ctx =
    List.fold_left (fun acc d ->
        Context.Rel.Declaration.fold_constr (fun c acc -> constr_names acc c) d acc)
      acc ctx
  in
  Array.fold_left (fun acc mip ->
      let acc = context acc mip.mind_arity_ctxt in
      let acc = constr_names acc mip.mind_user_arity in
      let acc = Array.fold_left constr_names acc mip.mind_user_lc in
      match mip.mind_record with
      | PrimRecord { tys; _ } -> Array.fold_left constr_names acc tys
      | NotRecord | FakeRecord -> acc)
    (context acc mib.mind_params_ctxt) mib.mind_packets

let rec signature_names acc = function
  | NoFunctor struc ->
    List.fold_left (fun acc (_, field) -> match field with
        | SFBconst cb -> const_names acc cb
        | SFBmind mib -> mind_names acc mib
        | SFBrules _ -> acc
        | SFBmodule mb -> signature_names acc (Mod_declarations.mod_type mb)
        | SFBmodtype mtb -> signature_names acc (Mod_declarations.mod_type mtb))
      acc struc
  | MoreFunctor (_, mtb, sign) ->
    signature_names (signature_names acc (Mod_declarations.mod_type mtb)) sign

let declaration_names ~constants ~inductives ~modtypes =
  let acc = List.fold_left (fun acc (_, _, cb) -> const_names acc cb) KerName.Set.empty constants in
  let acc = List.fold_left (fun acc (_, _, mib) -> mind_names acc mib) acc inductives in
  List.fold_left (fun acc (_, _, mtb) -> signature_names acc (Mod_declarations.mod_type mtb))
    acc modtypes

(************************************************************************)
(** {6 Module types}

    A field of a [Module Type] is not a constant of the environment, so the
    walk over the environment's constants does not see it. Each challenge
    module type is compared with the solution's module type of the same
    path, field by field.

    Of a module body ([module_type_body], or the [module_body] of a module
    field):
    - [mod_type], the expanded signature, is compared field by field;
    - [mod_type_alg], the algebraic form the signature was expanded from, is
      left out: the kernel keeps it for printing and extraction only;
    - [mod_delta], which names stand for which canonical names, is left out:
      the term comparison compares canonical names;
    - [mod_expr], the implementation of a module field, is left out: what a
      signature says of a module is its signature.
    Every kind of structure field is compared: [SFBconst], [SFBmind],
    [SFBrules] (by [rule_symbols]), [SFBmodule] and [SFBmodtype]. A functor
    is compared parameter by parameter, under the renaming of [umap.params].
    No environment holds the fields of a module type or the functor
    parameters, which a field's type may name, so a field is compared with
    no environment to type it in ([stated_sort]). *)

let rec eq_signature m s1 s2 =
  match s1, s2 with
  | NoFunctor b1, NoFunctor b2 -> eq_structure m b1 b2
  | MoreFunctor (p1, t1, s1), MoreFunctor (p2, t2, s2) ->
    (* The challenge's parameter [p1] stands for the solution's [p2] in the
       rest of the signature and in its own type, whose fields name one
       another under it. The solution's parameters in scope stay one-to-one
       with the challenge's: were [p2] bound again inside, a name under
       either binding would stand for both. *)
    if MBId.Set.mem p2 m.bound then diff "the solution binds one functor parameter twice";
    let mp2 = ModPath.MPbound p2 in
    (* [add_mbid], not [join]: each challenge parameter is renamed once, so
       one that has the name of a solution parameter is not renamed again. *)
    let params =
      Mod_subst.add_mbid p1 mp2 (Mod_subst.empty_delta_resolver mp2)
        (Option.default Mod_subst.empty_subst m.params)
    in
    let inner = { m with params = Some params; bound = MBId.Set.add p2 m.bound } in
    let inner = eq_modtype inner t1 t2 in
    let inner = eq_signature inner s1 s2 in
    { inner with params = m.params; bound = m.bound }
  | NoFunctor _, MoreFunctor _ -> diff "a module type is a functor in the solution"
  | MoreFunctor _, NoFunctor _ -> diff "a functor is not a functor in the solution"

and eq_structure m b1 b2 =
  List.fold_left (fun m (l, f1) ->
      match List.assoc_opt l b2 with
      | None -> diff "the field %s is missing from the solution" (Id.to_string l)
      | Some f2 ->
        match f1, f2 with
        (* A field of a module type is never a config-named theorem: the
           config names a constant of the environment. *)
        | SFBconst c1, SFBconst c2 ->
          (* never forced: with no environment, the first rule refuses a body *)
          eq_const_body ~env:None ~is_theorem:false ~named:(lazy true) m c1 c2
        | SFBmind i1, SFBmind i2 -> eq_mib_body m i1 i2
        | SFBrules r1, SFBrules r2 ->
          let symbols1 = List.map (rename m Mod_subst.subst_constant) (rule_symbols r1) in
          if not (CList.equal Constant.CanOrd.equal symbols1 (rule_symbols r2)) then
            diff "the field %s rewrites other symbols in the solution" (Id.to_string l);
          m
        | SFBmodule mb1, SFBmodule mb2 ->
          eq_signature m (Mod_declarations.mod_type mb1) (Mod_declarations.mod_type mb2)
        | SFBmodtype t1, SFBmodtype t2 -> eq_modtype m t1 t2
        | (SFBconst _ | SFBmind _ | SFBrules _ | SFBmodule _ | SFBmodtype _), _ ->
          diff "the field %s is of another kind in the solution" (Id.to_string l))
    m b1

and eq_modtype m t1 t2 =
  eq_signature m (Mod_declarations.mod_type t1) (Mod_declarations.mod_type t2)

(************************************************************************)
(** {6 The run} *)

type t = {
  cfg : config;
  dir : string;                  (** the challenge directory, as given *)
  files : (string * string) list;
      (** The challenge files, absolute or as given, each with the sha256
          that the config pins for it and that [prepare] found it has. *)
  challenge_dir : string option;
      (** The real path of the challenge directory. A challenge library under
          the root the challenge stands in for is read from below it, unless
          pre-checked ([check_challenge_place]). *)
  prechecked : DirPath.Set.t;
  challenge_root : DirPath.t;
      (** The logical root the challenge stands in for ([run]). A library
          under it is the solution's own. Every other library the solution
          loaded is a shared one, which [check_provenance] accepts only from
          a trusted directory ([trusted_dirs]) and from no place the
          solution's side can write ([solution_place]). *)
  open_roots : (DirPath.t * string) list;
      (** The roots the command line binds that the challenge does NOT stand
          in for, with the directory each is bound to. A library under one of
          them is the solution's side of the run and the challenge has no
          counterpart for it, so [check_open_roots] refuses the run unless
          the config pins it. *)
  cwd : string option;
      (** The real path of the working directory. The load path binds it
          implicitly and NOT recursively, so a library is found there only
          as a file directly in it. *)
  bound_dirs : string list;
      (** The real paths of the directories the command line binds, each
          with its subdirectories. *)
  trusted_dirs : string list;
      (** The real paths of the directories whose libraries the run takes
          for the installation's ([run]), each with its subdirectories. *)
  solution_libs : DirPath.t list;
      (** Every library the solution loaded, sorted by name. *)
  solution_deps : (DirPath.t * Safe_typing.vodigest) array DirPath.Map.t;
      (** The dependency digests each library the solution loaded records. *)
  prechecked_closure : DirPath.Set.t;
      (** The pre-checked libraries and every library they rest on, by the
          dependencies that [solution_deps] records ([deps_closure]): the
          closure [check_prechecked_deps] checks, so each of its libraries is
          one file for both sides or pinned by its sha256 as a challenge
          file. *)
  solution_files : string DirPath.Map.t;
      (** The file the loader recorded for each library the solution
          loaded. *)
}

let is_prechecked t dp = DirPath.Set.mem dp t.prechecked

let under_challenge_root t lib = CheckLibrary.under_root ~root:t.challenge_root lib

(* What a library is to the run: a pre-checked one, whose bytes the config
   pins, wherever it lies; otherwise the solution's own when it lies under
   the root the challenge stands in for, and a shared one when it does
   not. *)
type origin = Prechecked | Own | Shared

let origin t dp =
  if is_prechecked t dp then Prechecked
  else if under_challenge_root t dp then Own
  else Shared

let realpath p =
  try Some (Unix.realpath p) with Unix.Unix_error _ | Invalid_argument _ | Sys_error _ -> None

(* [same_real_file a b]: whether [a] and [b] resolve to one real path. [a] is
   resolved once, for a predicate applied to many [b]. A path that cannot be
   resolved is the same file as none. *)
let same_real_file a =
  match realpath a with
  | None -> fun _ -> false
  | Some ra -> fun b -> Option.equal String.equal (realpath b) (Some ra)

let path_under ~dir file =
  String.equal file dir || CString.is_prefix (Filename.concat dir "") file

(* The place a solution's file could have been found in that holds [file],
   the path the loader recorded: the working directory, for a file directly
   in it, or a directory the command line binds, for a file anywhere below
   it. Both the directory the loader found the file in, [found_in] (its real
   path), and the file's own real path are tested, so a link in such a place
   to a file elsewhere, or a link elsewhere to a file in one, is found. A
   path that cannot be resolved is in an unknown place, which counts as the
   solution's. [None]: in no such place. This says where the recorded file
   is, not who wrote it. *)
let solution_place t ~found_in file =
  match found_in, realpath file with
  | None, _ | _, None -> Some file
  | Some d, Some f ->
    let in_cwd p = match t.cwd with
      | Some c -> String.equal (Filename.dirname p) c || String.equal p c
      | None -> true
    in
    if in_cwd (Filename.concat d (Filename.basename file)) || in_cwd f then
      Some "the working directory"
    else
      List.find_map (fun dir ->
          if path_under ~dir d || path_under ~dir f then Some ("the bound directory " ^ dir)
          else None)
        t.bound_dirs

(* Whether a file was found in a trusted directory: [found_in], the real path
   of the directory the loader found it in, lies under the real path of one
   of [t.trusted_dirs]. That directory is the one tested, not the file's own
   real path, since an installation may hold its files as links to where
   they were built: a file link inside a trusted directory is placed by
   whoever writes that directory, whom the run trusts. A directory link is
   not taken as the trusted directory's: the load path stores each directory
   with links resolved ([CheckLibrary.add_load_path]), so a file found below
   a directory link was found in the link's target, which must itself lie
   under a trusted directory. A link in a place the solution's side can
   write is [solution_place]'s, which reads the file's own real path too. *)
let trusted_place t ~found_in =
  match found_in with
  | None -> false
  | Some d -> List.exists (fun dir -> path_under ~dir d) t.trusted_dirs

(* Refuses [file] as the file of the pre-checked library [p] unless it has
   the sha256 that the config pins for [p]. *)
let check_pin p file =
  let got = sha256_of_file file in
  if not (String.equal got p.pc_sha256) then
    CErrors.user_err
      (Pp.str ("The pre-checked library " ^ DirPath.to_string p.pc_library ^ " is " ^
               file ^ ", whose sha256 is " ^ got ^ ", and the config pins " ^
               p.pc_sha256 ^ "."))

(* The pre-checked libraries are resolved on the solution's load path, which
   is the one in place when this runs: before any library is read, and so
   before the file of a pre-checked library, which loads without a check, is
   unmarshalled. Every pin is checked before the names are returned, so the
   caller cannot have the libraries that load without a check apart from
   their pins. The loader resolves each name to the same file, unless the
   command line names a file of that library in a second directory bound to
   its logical path, which it then reads instead: [prepare] checks the pin
   on that file as well. *)
let check_prechecked cfg =
  List.iter (fun p -> check_pin p (CheckLibrary.library_file p.pc_library))
    cfg.cfg_prechecked;
  prechecked_libraries cfg

(* A root the command line binds that the challenge does not stand in for is
   an open root: the solution's build put files there, and the challenge
   directory holds nothing under it. Such a library is neither compared
   (the challenge has no counterpart) nor pinned, and loading it into the
   challenge environment as a shared one would let a file the solution
   wrote decide a universe constraint on BOTH sides, which is the forgery
   this refuses: the run stops unless the config pre-checks every library
   the solution loaded from under that root, which pins its sha256.

   A run as check_compare.mli describes binds one root, the solution's
   project root, which every checked solution library lives under and the
   challenge therefore stands in for, so the list is empty there. A test
   that binds a stand-in for installed libraries pre-checks them, as the
   config's pre-checked list is for. *)
let check_open_roots t =
  List.iter (fun lib ->
      List.iter (fun (root, path) ->
          if CheckLibrary.under_root ~root lib && not (is_prechecked t lib) then
            CErrors.user_err
              Pp.(str ("The solution loaded the library " ^ DirPath.to_string lib ^
                       " from " ^ path ^ ", bound to " ^ DirPath.to_string root ^
                       ", which the challenge does not stand in for and the config \
                        does not declare pre-checked. Every library of such a root \
                        must be pre-checked, so that its bytes are pinned.")))
        t.open_roots)
    t.solution_libs

let rec mp_root mp = match mp with
  | ModPath.MPfile dp -> Some dp
  | ModPath.MPdot (mp, _) -> mp_root mp
  | ModPath.MPbound _ -> None

let in_libs libs mp = match mp_root mp with
  | None -> false
  | Some dp -> DirPath.Set.mem dp libs

(* A library that is one file for both sides: a pre-checked one, whose bytes
   the config pins, or a shared one that the solution loaded: outside the
   root the challenge stands in for, from a recorded file in a trusted
   directory and in no place a solution's file is found in. [prepare]
   refuses a run that loaded a shared library from anywhere else
   ([check_provenance]) before anything asks this. What this establishes is
   where the loaded file is, from the path the loader recorded; that no
   solution wrote such a file rests on whoever starts the run keeping the
   trusted directories out of the solution's reach (check_compare.mli). The
   challenge load reads a pre-checked library from the solution's file or
   from a file of the pinned sha256, and a shared library from the
   solution's file ([check_same_files]). *)
let one_file t dp = match origin t dp with
  | Prechecked -> true
  | Own -> false
  | Shared -> DirPath.Map.mem dp t.solution_files

let rooted_one_file t mp = match mp_root mp with
  | None -> false
  | Some dp -> one_file t dp

(* A library a side loaded that is neither under the root the challenge
   stands in for nor pre-checked counts as the installation's, so its file
   must have been found in a trusted directory ([trusted_place]) and in no
   place a solution's file is found in ([solution_place]): otherwise a file
   the solution's side wrote in a directory the load path binds without a
   [-Q], such as the working directory or an XDG directory, could stand in
   for an installed library of the same name. [libs] are a side's loaded
   libraries with the files the loader recorded. *)
let check_provenance t ~side libs =
  List.iter (fun (dp, file) ->
      match origin t dp with
      | Prechecked | Own -> ()
      | Shared ->
        let found_in = realpath (Filename.dirname file) in
        match solution_place t ~found_in file with
        | Some place ->
          CErrors.user_err
            Pp.(str ("The " ^ side ^ " loaded the library " ^ DirPath.to_string dp ^
                     " from " ^ file ^ ", in " ^ place ^ ", where a solution's files are \
                      found. No root the challenge stands in for holds it and the config \
                      does not pre-check it, so it would count as an installed one. A \
                      -compare run refuses it."))
        | None ->
          if not (trusted_place t ~found_in) then
            let trusted = match t.trusted_dirs with
              | [] -> "none in this run"
              | l -> String.concat ", " l
            in
            CErrors.user_err
              Pp.(str ("The " ^ side ^ " loaded the library " ^ DirPath.to_string dp ^
                       " from " ^ file ^ ", which is under none of the directories a \
                        -compare run trusts for a library that no root the challenge \
                        stands in for holds and the config does not pre-check: the \
                        corelib directory, user-contrib and the directories of ROCQPATH \
                        and COQPATH (" ^ trusted ^ "). A -compare run refuses it.")))
    libs

(* [roots] and every library they rest on: the dependencies that [deps]
   records for each library of the closure, transitively. *)
let deps_closure deps roots =
  let rec walk acc = function
    | [] -> acc
    | dp :: tl ->
      if DirPath.Set.mem dp acc then walk acc tl
      else
        let next = match DirPath.Map.find_opt dp deps with
          | None -> []
          | Some a -> Array.to_list (Array.map fst a)
        in
        walk (DirPath.Set.add dp acc) (next @ tl)
  in
  walk DirPath.Set.empty roots

(* Whether the library [dp] the solution loaded is pinned by its sha256 as a
   challenge file (the rule of [run], check_compare.mli). The path of its
   file below the challenge directory and the config's paths are compared
   by real path, so a config path may use either separator on Windows. *)
let pinned t dp =
  match DirPath.Map.find_opt dp t.solution_files,
        CheckLibrary.vo_path_below ~root:t.challenge_root dp with
  | None, _ | _, None -> false
  | Some file, Some path ->
    let same = same_real_file (CUnix.correct_path path t.dir) in
    let sha256 = lazy (sha256_of_file file) in
    List.exists (fun (f, h) -> same f && String.equal h (Lazy.force sha256)) t.files

(* The rule of [run] for the libraries a pre-checked one rests on
   (check_compare.mli), on [prechecked_closure]. When several libraries
   fail, the one refused is the first in the set's order; the message names
   the first pre-checked library, in the config's order, that rests on it,
   which exists since the closure of the list is the union of each
   library's. *)
let check_prechecked_deps t =
  DirPath.Set.iter (fun dep ->
      if not (one_file t dep || pinned t dep) then
        let p =
          List.find (fun p -> DirPath.Set.mem dep (deps_closure t.solution_deps [p]))
            (prechecked_libraries t.cfg)
        in
        CErrors.user_err
          Pp.(str ("The pre-checked library " ^ DirPath.to_string p ^
                   " depends on the library " ^ DirPath.to_string dep ^
                   ", which is neither pre-checked by the config, nor pinned by its \
                    sha256 as a challenge file, nor from the installed load path. The \
                    digest the pre-checked library records for it pins nothing: a \
                    library's digest is the one its own file states. A kernel check \
                    of it is not enough either, since the pre-checked library was not \
                    checked against it. A -compare run refuses it.")))
    t.prechecked_closure

(* The rule of [run] for the libraries the solution loaded without a check
   (check_compare.mli). *)
let check_unchecked t ~admitted =
  let admitted = DirPath.Set.of_list admitted in
  List.iter (fun dp ->
      match origin t dp with
      | Prechecked | Shared -> ()
      | Own ->
        if not (DirPath.Set.mem dp admitted || pinned t dp) then
          CErrors.user_err
            Pp.(str ("The solution library " ^ DirPath.to_string dp ^ " was loaded without \
                      a check, as a dependency of a library given with -norec or -admit, \
                      and it is neither pre-checked by the config, nor pinned by its \
                      sha256 as a challenge file, nor given with -admit itself. A \
                      -compare run refuses it.")))
    (CheckLibrary.unchecked ())

(* The challenge load puts the challenge directory in front of the
   solution's directories under the root it stands in for, and leaves
   those behind it: a challenge library that the directory does not hold
   would be read from the solution's file and then compared with itself.
   So a library the challenge loaded under that root must have been read
   from a file below the challenge directory (real paths, links resolved),
   unless it is pre-checked: a pre-checked library may resolve to the
   solution's file, and [check_same_files] tests that it is read from
   pinned bytes. [libs] are the challenge's loaded libraries with the files
   the loader recorded. *)
let check_challenge_place t libs =
  List.iter (fun (dp, file) ->
      match origin t dp with
      | Prechecked | Shared -> ()
      | Own ->
        let inside = match t.challenge_dir, realpath file with
          | Some dir, Some f -> path_under ~dir f
          | None, _ | _, None -> false
        in
        if not inside then
          CErrors.user_err
            Pp.(str ("The challenge loaded the library " ^ DirPath.to_string dp ^ " from " ^
                     file ^ ", which is not under the challenge directory. A challenge \
                      library under a root the challenge stands in for is read from the \
                      challenge directory unless it is pre-checked. A -compare run \
                      refuses it.")))
    libs

(* The file the solution loaded the pre-checked library [dp] from. Every
   pre-checked library is on the admit list ([check_prechecked]), which a
   -compare run reads, so the solution loaded each one. A missing one is an
   anomaly rather than a pass: a pin passed over in silence is a check that
   did not run. *)
let prechecked_solution_file t dp =
  match DirPath.Map.find_opt dp t.solution_files with
  | Some file -> file
  | None ->
    CErrors.anomaly
      Pp.(str ("The solution did not load the pre-checked library " ^
               DirPath.to_string dp ^ ", which is on the admit list that a -compare \
                run reads."))

(* A library that is one file for both sides ([one_file]) is so only if the
   challenge load reads it from the file the solution read. The challenge's
   load path is the solution's with the challenge directory bound in front
   under the root it stands in for, but that binding can take a directory
   from another logical path (a link in the challenge directory to a
   directory the load path already binds), and a name the two sides share
   may then resolve to another file. So each shared library the solution
   loaded too, and each pre-checked library, must come from the solution's
   file, by real path. A pre-checked library may also come from another
   file of the pinned sha256, such as a copy in the challenge directory:
   the solution's file has that sha256 as well ([check_prechecked] or
   [prepare] compared it), so either way the bytes are pinned. [libs] are
   the challenge's loaded libraries with the files the loader recorded. *)
let check_same_files t libs =
  List.iter (fun (dp, file) ->
      match origin t dp with
      | Own -> ()
      | Shared ->
        (match DirPath.Map.find_opt dp t.solution_files with
         | Some sol_file when not (same_real_file file sol_file) ->
           CErrors.user_err
             Pp.(str ("The challenge loaded the shared library " ^ DirPath.to_string dp ^
                      " from " ^ file ^ ", and the solution loaded it from " ^ sol_file ^
                      ": the two sides would read different files under one library \
                       name. A -compare run refuses it."))
         | Some _ | None -> ())
      | Prechecked ->
        if not (same_real_file (prechecked_solution_file t dp) file) then
          let got = sha256_of_file file in
          let pins p = DirPath.equal p.pc_library dp && String.equal p.pc_sha256 got in
          if not (List.exists pins t.cfg.cfg_prechecked) then
            CErrors.user_err
              Pp.(str ("The challenge loaded the pre-checked library " ^ DirPath.to_string dp ^
                       " from " ^ file ^ ", which is not the file the solution loaded it \
                        from, and whose sha256 is " ^ got ^ ", not the one the config \
                        pins. A -compare run refuses it.")))
    libs

(* Before the challenge is loaded: the files the config pins must be there
   and have the sha256 it gives, the file the solution read each pre-checked
   library from must have its pinned sha256, and the libraries the solution
   loaded must pass [check_open_roots], [check_provenance],
   [check_prechecked_deps] and [check_unchecked], in that order.
   [check_prechecked] ran before any library was read, on the file each
   pre-checked name resolved to then, which the loader may not have read:
   only a file the loader read in its place is hashed here. The load path
   has not changed since, so the name still resolves to the file hashed
   then. *)
let prepare cfg ~dir ~challenge_root ~open_roots ~bound_dirs ~trusted ~admitted =
  let files =
    List.map (fun f ->
        let p = CUnix.correct_path f.cf_path dir in
        if not (Sys.file_exists p) then
          CErrors.user_err Pp.(str ("The challenge file " ^ p ^ " is not there."));
        let got = sha256_of_file p in
        if not (String.equal got f.cf_sha256) then
          CErrors.user_err
            (Pp.str ("The challenge file " ^ p ^ " has sha256 " ^ got ^
                     ", and the config pins " ^ f.cf_sha256 ^ "."));
        p, f.cf_sha256)
      cfg.cfg_challenge_files
  in
  let loaded = CheckLibrary.loaded () in
  let solution_files = CheckLibrary.files_of loaded in
  let solution_deps = DirPath.Map.of_list (CheckLibrary.deps_of loaded) in
  let t =
    { cfg; dir; files; challenge_dir = realpath dir;
      prechecked = DirPath.Set.of_list (prechecked_libraries cfg);
      challenge_root; open_roots;
      cwd = realpath (Sys.getcwd ());
      bound_dirs = List.filter_map realpath bound_dirs;
      trusted_dirs = List.filter_map realpath trusted;
      solution_libs = List.map fst loaded;
      solution_deps;
      prechecked_closure = deps_closure solution_deps (prechecked_libraries cfg);
      solution_files = DirPath.Map.of_list solution_files }
  in
  List.iter (fun p ->
      let file = prechecked_solution_file t p.pc_library in
      if not (same_real_file (CheckLibrary.library_file p.pc_library) file) then
        check_pin p file)
    cfg.cfg_prechecked;
  check_open_roots t;
  check_provenance t ~side:"solution" solution_files;
  check_prechecked_deps t;
  check_unchecked t ~admitted;
  t

(* The dependency digests a challenge library and its solution library
   record for a library both sides load from one file ([one_file]) must be
   equal: otherwise the two sides were built against different copies of
   it, and their kernel names would name different objects. Checked before
   the challenge is imported. *)
let check_dep_digests t ~challenge ~solution =
  let digest_of deps dp =
    Array.fold_left (fun acc (d, dg) -> if DirPath.equal d dp then Some dg else acc) None deps
  in
  List.iter (fun (lib, ch_deps) ->
      match DirPath.Map.find_opt lib solution with
      | None -> ()
      | Some sol_deps ->
        Array.iter (fun (dep, ch_digest) ->
            if one_file t dep then
              let prechecked = is_prechecked t dep in
              match digest_of sol_deps dep with
              | Some sol_digest
                when not (Safe_typing.digest_match ~actual:sol_digest ~required:ch_digest) ->
                CErrors.user_err
                  Pp.(str ("The library " ^ DirPath.to_string lib ^
                           " depends on the " ^
                           (if prechecked then "pre-checked" else "shared") ^
                           " library " ^ DirPath.to_string dep ^
                           " with a different digest on the challenge side and on the \
                            solution side."))
              | _ -> ())
          ch_deps)
    challenge

(* The challenge load, between two swaps of the per-library tables: the
   challenge libraries have the solution's names, so they need tables of
   their own ([CheckLibrary.tables]).

   Besides the challenge files' closure, which alone is compared, the
   challenge environment loads the shared libraries the solution loaded, so
   that a constraint one of them carries is not read as one the solution
   added: what is left for the constraint checks is what the solution's own
   libraries add. A shared library that only the solution Requires is one
   file for both sides because every library naming it records the same
   digest on both sides ([check_dep_digests]), because the challenge load
   reads it from the solution's file ([check_same_files]), and because no
   bound root is left open ([check_open_roots]). [check_same_files] also
   tests that each pre-checked library the challenge loads is read from
   pinned bytes. It runs once the digests are compared, so that two sides
   built against two libraries of one name are reported as such.
   Every refusal comes before the import. Returns the challenge environment
   and the libraries of the files' closure. *)
let load_challenge t ~add_load_path senv0 =
  let saved = CheckLibrary.swap_tables (CheckLibrary.fresh_tables ()) in
  let restore () = ignore (CheckLibrary.swap_tables saved) in
  Fun.protect ~finally:restore (fun () ->
      add_load_path ~unix_path:t.dir ~rocq_root:t.challenge_root;
      (* A pre-checked library is not a shared one ([check_prechecked]). *)
      let shared =
        List.filter (fun dp -> match origin t dp with
            | Shared -> true
            | Prechecked | Own -> false)
          t.solution_libs
      in
      let needed, all = CheckLibrary.intern_challenge (List.map fst t.files) shared in
      let files = CheckLibrary.files_of all in
      check_challenge_place t files;
      check_provenance t ~side:"challenge" files;
      check_dep_digests t ~challenge:(CheckLibrary.deps_of all) ~solution:t.solution_deps;
      check_same_files t files;
      let senv = CheckLibrary.import_challenge senv0 all in
      Safe_typing.env_of_safe_env senv, DirPath.Set.of_list (List.map fst needed))

(************************************************************************)
(** {6 Comparing the two environments} *)

type failure = { f_name : string; f_reason : string }

(* The identity seed: a level or a global quality of a library that is one
   file for both sides ([one_file]), or a library a pre-checked one rests
   on ([prechecked_closure], whose doc says why both sides read the same
   bytes of it), when both environments hold it.

   A level no compared declaration names is in the map only through this:
   the body of an opaque proof is never compared, so a challenge proof's
   constraint on such a level would otherwise never be asked of the
   solution. So is a quality that no compared declaration names: a
   constraint that a solution library adds on it is still compared
   ([check_elim_constraints]).

   With the libraries a pre-checked one rests on, the map holds every
   quality that a compared statement stands on. A compared declaration
   names declarations of the challenge files' closure only. Each of those
   is compared, which maps the qualities it names, unless [run] skips its
   library, which [prechecked_closure] then holds. A skipped library names
   its own qualities and those of the libraries it rests on, which
   [prechecked_closure] holds too. So a sort that a challenge library
   declares and only a pre-checked library names, as the sort of one of
   its inductive types, is in the map, and a constraint that the solution
   adds on it is compared. *)
let seed_umap t ~challenge_env ~solution_env =
  let seeded dp = one_file t dp || DirPath.Set.mem dp t.prechecked_closure in
  let gch = Environ.universes challenge_env and gsol = Environ.universes solution_env in
  let sol = UGraph.domain gsol in
  let m =
    Univ.Level.Set.fold (fun u m ->
        match Univ.Level.name u with
        | None -> m
        | Some ug ->
          let dp, _, _ = Univ.UGlobal.repr ug in
          if seeded dp && Univ.Level.Set.mem u sol then add_level m u u else m)
      (UGraph.domain gch) empty_umap
  in
  let qsol = QGraph.domain (Environ.qualities solution_env) in
  Sorts.Quality.Set.fold (fun q m ->
      match q with
      | Sorts.Quality.QGlobal g ->
        let dp, _ = Sorts.QGlobal.repr g in
        if seeded dp && Sorts.Quality.Set.mem q qsol then add_quality m q q else m
      | Sorts.Quality.QConstant _ | Sorts.Quality.QVar _ -> m)
    (QGraph.domain (Environ.qualities challenge_env)) m

(* The reason a failing set of constraints gives: the first [shown] of them
   in sorted order, and how many more there are. *)
let constraints_reason bad =
  let shown = 5 in
  match List.sort String.compare bad with
  | [] -> None
  | l ->
    let n = List.length l in
    let head = CList.firstn (min shown n) l in
    Some (Printf.sprintf "the constraint %s does not hold on the other side%s"
            (String.concat ", " head)
            (if n > shown then Printf.sprintf " (and %d more)" (n - shown) else ""))

(* The outcome of [check_constraints]. *)
type universe_check =
  | Holds
  | Fails of string
  | Tolerated of string
      (** the solution-to-challenge direction fails, and the config tolerates
          [universe_constraints_flag]: the summary of what it skipped *)

(* The two directions are not the same question.

   Every challenge constraint, mapped, must hold in the solution: the
   solution must stand where the challenge stands. It is also where a
   solution that contradicts the challenge is caught: the solution's graph
   alone is consistent, since the kernel checked it, so if the solution
   entails every challenge constraint the union of the two is satisfiable.

   The other direction asks what the solution ADDS, and passes over one
   shape alone: a constraint between two levels of libraries outside the
   challenge's root. A proof adds those as a matter of course -- it
   instantiates installed definitions, and the kernel records what that
   costs -- and they say nothing about the challenge, since its statements
   do not stand on those levels relative to each other. A proof that
   applies a lemma of one installed library to a type of another records a
   constraint such as [A.u <= B.v] between a level of each; refusing it
   would fail every theorem of the run on that one line, and a file that
   restates the challenge's theorems and proves them with the solution's
   lemmas would have the kernel add the same constraint.

   Every other pair is compared, the challenge's own levels to each other
   AND to the installed ones. A solution that relates one of the
   challenge's own universes to an installed one has fixed where that
   universe sits, and a statement over it then says less than the
   challenge's does: a statement that injects Type@{u} into a type at an
   installed level is not provable while u and that level are apart, and is
   provable once the solution puts u below it. That is a forgery, and it
   carries no Constraint command: the Qed records it.

   A config that tolerates [universe_constraints_flag] skips this direction
   alone, and only once the challenge-to-solution direction has passed; the
   declaration comparison, the axiom checks and the kernel check are
   untouched. The flag is recorded on every theorem the solution holds only
   when this direction would have failed. Its object is the bounded summary
   of the skipped constraints, so a passing verdict says what it cost.

   Both directions compare the PROJECTION of one graph onto the mapped
   levels ([constraints_for], which walks on through a level it does not
   keep), so a path through levels the map does not hold is compared like a
   direct edge, and a forgery cannot be routed around.

   Every failing constraint is reported, not the first: a run that names one
   costs another run to learn whether there are more. *)
let check_constraints t ~challenge_env ~solution_env m =
  let gch = Environ.universes challenge_env and gsol = Environ.universes solution_env in
  let own u = match Univ.Level.name u with
    | None -> false
    | Some ug -> let dp, _, _ = Univ.UGlobal.repr ug in under_challenge_root t dp
  in
  let kept_ch = Univ.Level.Map.domain m.fwd and kept_sol = Univ.Level.Map.domain m.bwd in
  (* [constraints_for ~kept] emits only constraints between kept levels, and
     the kept set IS the map's domain, so a level the map does not hold
     cannot reach here. It is an anomaly rather than a pass: a constraint
     passed over in silence is a check that did not run. *)
  let mapped map u = match Univ.Level.Map.find_opt u map with
    | Some v -> v
    | None ->
      CErrors.anomaly
        Pp.(str ("The comparator projected a universe constraint onto " ^
                 Univ.Level.to_string u ^ ", which its level map does not hold."))
  in
  let fails ~skip map graph cs =
    constraints_reason (Univ.UnivConstraints.fold (fun (u, k, v) acc ->
        let u' = mapped map u and v' = mapped map v in
        if skip u' v' || UGraph.check_constraint graph (u', k, v') then acc
        else
          Printf.sprintf "%s%s%s"
            (Univ.Level.to_string u)
            (Pp.string_of_ppcmds (Univ.UnivConstraint.pr_kind k))
            (Univ.Level.to_string v) :: acc)
        cs [])
  in
  let never _ _ = false in
  match fails ~skip:never m.fwd gsol (UGraph.constraints_for ~kept:kept_ch gch) with
  | Some e -> Fails ("the challenge has a universe constraint the solution does not: " ^ e)
  | None ->
    let neither_own u' v' = not (own u') && not (own v') in
    match fails ~skip:neither_own m.bwd gch (UGraph.constraints_for ~kept:kept_sol gsol) with
    | Some e when List.mem_assoc universe_constraints_flag t.cfg.cfg_flags -> Tolerated e
    | Some e -> Fails ("the solution has a universe constraint the challenge does not: " ^ e)
    | None -> Holds

(* The elimination constraints between sort qualities, in the two
   directions of [check_constraints]. A library may declare a global sort
   quality ([Sort s.]) and constraints on it ([Constraint s -> Prop.]), and
   the environment's quality graph ([Environ.qualities]) holds those of
   every loaded library. A solution library that adds [s -> Prop] for a sort
   [s] that stands for one of the challenge's lets a proof eliminate a type
   of sort [s] into [Prop], which the challenge's statements over its sort
   did not allow; every declaration still compares equal, and only the
   graphs show it.

   A global quality is named by its library and its rank among the
   library's [Sort] commands, which the two sides need not share, so the
   graphs are compared through the quality map, as [check_constraints]
   compares the universe graphs through the level map. Both directions
   compare the PROJECTION of one graph onto the constants and the
   qualities the map holds, mapped: a quality the map does not hold -- one
   that only the solution declares, or one of the challenge's that no
   compared declaration names and [seed_umap] does not hold, on which no
   compared statement stands -- is walked through, so a path through it is
   compared like a direct edge.

   Challenge to solution: every constraint of the challenge's graph, so
   projected, must hold in the solution's graph.

   Solution to challenge: every constraint of the solution's graph, so
   projected, must hold in the challenge's graph, whichever library
   declares the qualities. Unlike the universe check, no shape is passed
   over. A proof never adds an elimination constraint: only a [Constraint]
   command does, and the challenge environment loads the shared libraries
   the solution loaded, so the solution's graph holds no constraint the
   challenge's lacks unless a file the challenge does not load, one of the
   solution's, states it. Such a file may state one on any library's sort:
   one of the challenge's, or one of an installed or pre-checked library or
   of a library a pre-checked one rests on ([Constraint V.s -> Prop.]),
   which the map holds as itself ([seed_umap]) and on which the
   challenge's statements stand as much.
   [universe_constraints_flag] does not skip this direction: it stays
   strict.

   [QGraph.constraints_for ~kept] (qGraph.ml) is the projection that
   [UGraph.constraints_for] makes, by the same
   [AcyclicGraph.constraints_for]: a path through qualities it does not
   keep comes out as a direct constraint, and an equivalence between two
   kept qualities as a constraint each way. A kept quality must be in the
   graph, hence the filter on its domain.

   Both graphs are read with their constraints in force: in an environment
   that does not check eliminations, [QGraph.check_constraint] accepts every
   constraint, which would leave nothing compared. *)
let check_elim_constraints ~challenge_env ~solution_env m =
  let enforced env = QGraph.set_ignore_constraints false (Environ.qualities env) in
  let gch = enforced challenge_env and gsol = enforced solution_env in
  (* The kept set is the constants and the map's domain, so a quality the
     map does not hold cannot reach here, as in [check_constraints]. *)
  let mapped map q = match q with
    | Sorts.Quality.QConstant _ -> q
    | Sorts.Quality.QGlobal _ | Sorts.Quality.QVar _ ->
      match Sorts.Quality.Map.find_opt q map with
      | Some q' -> q'
      | None ->
        CErrors.anomaly
          Pp.(str ("The comparator projected an elimination constraint onto " ^
                   quality_name q ^ ", which its quality map does not hold."))
  in
  let fails map graph cs =
    constraints_reason (Sorts.ElimConstraints.fold (fun (q1, k, q2) acc ->
        let q1' = mapped map q1 and q2' = mapped map q2 in
        if QGraph.mem q1' graph && QGraph.mem q2' graph
           && QGraph.check_constraint graph (q1', k, q2')
        then acc
        else
          Printf.sprintf "%s %s %s"
            (quality_name q1) (Pp.string_of_ppcmds (Sorts.ElimConstraint.pr_kind k))
            (quality_name q2) :: acc)
        cs [])
  in
  let kept map graph =
    Sorts.Quality.Set.filter (fun q -> Sorts.Quality.is_qconst q || Sorts.Quality.Map.mem q map)
      (QGraph.domain graph)
  in
  match fails m.qfwd gsol (QGraph.constraints_for ~kept:(kept m.qfwd gch) gch) with
  | Some e -> Some ("the challenge has an elimination constraint the solution does not: " ^ e)
  | None ->
    match fails m.qbwd gch (QGraph.constraints_for ~kept:(kept m.qbwd gsol) gsol) with
    | Some e -> Some ("the solution has an elimination constraint the challenge does not: " ^ e)
    | None -> None

(* The module types a library's signature declares, each with its printed
   name and its path: the module type fields of the library and of its
   modules, at any depth, which are the module types the environment holds
   for it ([Modops.add_structure]). A functor's body is not walked: the
   environment holds none of its fields either. *)
let rec signature_modtypes mp acc = function
  | MoreFunctor _ -> acc
  | NoFunctor struc ->
    List.fold_left (fun acc (l, field) ->
        let mp' = ModPath.MPdot (mp, l) in
        match field with
        | SFBmodtype mtb -> (ModPath.to_string mp', mp', mtb) :: acc
        | SFBmodule mb -> signature_modtypes mp' acc (Mod_declarations.mod_type mb)
        | SFBconst _ | SFBmind _ | SFBrules _ -> acc)
      acc struc

(* The primitive type that the kernel registers the constant [c] as in
   [env] ([Primitive int := #int63_type]), if any: the kernel gives each
   literal of that type the type [c], by its canonical name, as conversion
   compares constants. The kernel's registrations of inductive types are
   not read: they choose the inductive type in which a primitive operation
   builds its result, and a primitive operation is a [Primitive] constant,
   held to the challenge's operation and type when the challenge declares
   it, and an axiom of the closure otherwise. *)
let primitive_type env c =
  let[@warning "+9"] Retroknowledge.{
      retro_int63; retro_float64; retro_string; retro_array;
      retro_bool = _; retro_carry = _; retro_pair = _; retro_cmp = _; retro_f_cmp = _;
      retro_f_class = _;
    } = Environ.retroknowledge env
  in
  let is = function Some c' -> Constant.CanOrd.equal c c' | None -> false in
  let open CPrimitives in
  if is retro_int63 then Some (prim_type_to_string PT_int63)
  else if is retro_float64 then Some (prim_type_to_string PT_float64)
  else if is retro_string then Some (prim_type_to_string PT_string)
  else if is retro_array then Some (prim_type_to_string PT_array)
  else None

(* A compared constant is the same primitive type on both sides, or none on
   either. A primitive type's body is [Undef], as a parameter's, so
   [eq_const_body] does not see the difference, which changes what the
   constant is: a parameter that the solution registered as a primitive
   type would have literals, so the solution could prove it inhabited. *)
let eq_primitive_type ~challenge_env ~solution_env c =
  let t1 = primitive_type challenge_env c and t2 = primitive_type solution_env c in
  if not (Option.equal String.equal t1 t2) then
    let name = function Some t -> "the primitive type #" ^ t | None -> "no primitive type" in
    diff "this constant is %s in the challenge and %s in the solution" (name t1) (name t2)

(* Every challenge declaration of [libs]: the constants, then the inductive
   blocks, then the module types, each kind in the order their printed names
   sort, the kernel name deciding between two that print alike. The order
   decides which difference a theorem's reason names first, and in which
   order the level and quality maps are built. A declaration the solution
   does not hold is a failure; a declaration only the solution holds is not
   visited. Returns the failures, in the order they are found, and the
   maps. *)
let compare_declarations t ~challenge_env ~solution_env ~libs ~theorems =
  let m = ref (seed_umap t ~challenge_env ~solution_env) in
  let failures = ref [] in
  let fail name reason = failures := { f_name = name; f_reason = reason } :: !failures in
  let deferred = ref [] in
  let step name f =
    match f !m with
    | m' -> m := m'
    | exception Diff d -> fail name d
    | exception Undecided d -> deferred := (name, f, d) :: !deferred
  in
  let by_name compare l =
    List.sort (fun (n1, k1, _) (n2, k2, _) ->
        let c = String.compare n1 n2 in
        if Int.equal c 0 then compare k1 k2 else c)
      l
  in
  let constants =
    Environ.fold_constants (fun c cb acc ->
        if in_libs libs (Constant.modpath c) then (Constant.to_string c, c, cb) :: acc
        else acc)
      challenge_env []
  in
  let inductives =
    Environ.fold_inductives (fun i mib acc ->
        if in_libs libs (MutInd.modpath i) then (MutInd.to_string i, i, mib) :: acc
        else acc)
      challenge_env []
  in
  let modtypes =
    DirPath.Set.fold (fun dp acc ->
        let mp = ModPath.MPfile dp in
        match Environ.lookup_module mp challenge_env with
        | mb -> signature_modtypes mp acc (Mod_declarations.mod_type mb)
        | exception Not_found ->
          CErrors.anomaly
            Pp.(str ("The challenge environment does not hold the library " ^
                     DirPath.to_string dp ^ ", which the challenge loaded.")))
      libs []
  in
  (* forced only by a challenge constant without a body, which the challenge
     does not state as data, that the solution gives a transparent one *)
  let names = lazy (declaration_names ~constants ~inductives ~modtypes) in
  List.iter (fun (name, c, cb) ->
      match Environ.lookup_constant_opt c solution_env with
      | None -> fail name "missing"
      | Some cb' ->
        let named = lazy (let names = Lazy.force names in
                          KerName.Set.mem (Constant.user c) names
                          || KerName.Set.mem (Constant.canonical c) names)
        in
        step name (fun m ->
            eq_primitive_type ~challenge_env ~solution_env c;
            eq_const_body ~env:(Some challenge_env)
              ~is_theorem:(CString.Set.mem name theorems) ~named m cb cb'))
    (by_name Constant.UserOrd.compare constants);
  List.iter (fun (name, i, mib) ->
      if not (Environ.mem_mind i solution_env) then fail name "missing"
      else
        let mib' = Environ.lookup_mind i solution_env in
        step name (fun m -> eq_mib_body m mib mib'))
    (by_name MutInd.UserOrd.compare inductives);
  List.iter (fun (name, mp, mt) ->
      match Environ.lookup_modtype mp solution_env with
      | mt' -> step name (fun m -> eq_modtype m mt mt')
      | exception Not_found -> fail name "missing")
    (by_name ModPath.compare modtypes);
  (* The declarations set aside as undecided, again, until a pass decides
     none of them. Then the first of them that a tie decides
     ([map_through_constraints]) is compared with ties allowed, and the
     passes resume without them: a tie is the last resort, taken only where
     no comparison maps the level or quality otherwise. Each pending entry
     keeps the reason of its last comparison, so what is still undecided
     fails with that reason; no declaration is left both uncompared and
     unfailed. *)
  let attempt ~ties (name, f, _) =
    match f { !m with ties } with
    | m' -> m := { m' with ties = false }; None
    | exception Diff d -> fail name d; None
    | exception Undecided d -> Some (name, f, d)
  in
  let rec again pending =
    let still = CList.map_filter (attempt ~ties:false) pending in
    if List.length still < List.length pending then again still else tie [] still
  and tie seen = function
    | [] -> List.iter (fun (name, _, d) -> fail name d) (List.rev seen)
    | e :: rest ->
      match attempt ~ties:true e with
      | None -> again (List.rev_append seen rest)
      | Some e -> tie (e :: seen) rest
  in
  again (List.rev !deferred);
  List.rev !failures, !m

(************************************************************************)
(** {6 The verdict} *)

(* Every constant of [env] under the name it prints. Two constants can print
   the same name (the constant [thm] of a module [Q] of the library [R.P]
   and the constant [thm] of the library [R.P.Q]), so a name maps to all of
   them. *)
let constant_index env =
  Environ.fold_constants (fun c _ acc ->
      CString.Map.update (Constant.to_string c)
        (fun l -> Some (c :: Option.default [] l)) acc)
    env CString.Map.empty

(* Where an object lives, in words, for a refusal: "the constant g of
   module Q of the library R.P". *)
let describe_object obj =
  let rec path = function
    | ModPath.MPfile dp -> "the library " ^ DirPath.to_string dp
    | ModPath.MPdot (mp, l) -> "module " ^ Id.to_string l ^ " of " ^ path mp
    | ModPath.MPbound _ as mp -> "the functor parameter " ^ ModPath.to_string mp
  in
  match obj with
  | GlobRef.ConstRef c ->
    "the constant " ^ Id.to_string (Constant.label c) ^ " of " ^ path (Constant.modpath c)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    "the inductive block " ^ Id.to_string (MutInd.label mind) ^ " of " ^ path (MutInd.modpath mind)
  | GlobRef.VarRef id -> "the section variable " ^ Id.to_string id

(* The first rewrite rule a module declares, as the symbol it rewrites. A
   rule lives in a structure field ([SFBrules]): the kernel refuses one in a
   section. The walk reads the declarations themselves, not the
   environment's table of rules, which is keyed by the symbol a rule
   rewrites: a rule may rewrite a symbol of another library, and a module
   sealed by a signature that hides its rule puts no rule in the
   environment at all, though its body was checked with the rule in force.
   So it reads the signature, the structure that implements it, submodules,
   functor parameters and module types. A rule a signature declares counts
   as well, the module that implements it with definitions included: the
   environment rewrites by it. A [Symbol] declaration is a constant, not a
   rule: it is an assumption, which the axiom check counts. *)
let rec rule_in_signature = function
  | NoFunctor struc -> rule_in_structure struc
  | MoreFunctor (_, mtb, sign) ->
    (match rule_in_signature (Mod_declarations.mod_type mtb) with
     | Some _ as r -> r
     | None -> rule_in_signature sign)

and rule_in_structure struc =
  List.find_map (fun (_, field) -> match field with
      | SFBrules { rewrules_rules = (c, _) :: _ } -> Some c
      | SFBrules { rewrules_rules = [] } | SFBconst _ | SFBmind _ -> None
      | SFBmodule mb -> rule_in_module mb
      | SFBmodtype mtb -> rule_in_signature (Mod_declarations.mod_type mtb))
    struc

and rule_in_module mb =
  match rule_in_signature (Mod_declarations.mod_type mb) with
  | Some _ as r -> r
  | None ->
    match Mod_declarations.mod_expr mb with
    | Mod_declarations.Struct (_, struc) -> rule_in_structure struc
    (* [Abstract] has no implementation, [FullStruct]'s is the signature
       just read, and [Algebraic]'s holds no field: its rules are those of
       the modules it names, each walked where it is declared. *)
    | Mod_declarations.(Abstract | Algebraic _ | FullStruct) -> None

(* The first rewrite rule one of [libs] declares, in the solution's
   environment, which holds every library the solution loaded. *)
let solution_rewrite_rule env libs =
  List.find_map (fun dp ->
      match Environ.lookup_module (ModPath.MPfile dp) env with
      | mb -> rule_in_module mb
      | exception Not_found ->
        CErrors.user_err
          Pp.(str ("The solution loaded the library " ^ DirPath.to_string dp ^
                   ", which its environment does not hold.")))
    libs

(* A permitted axiom is a declaration the challenge hands the solution, so
   it is matched by its kernel name, not by the name it prints: a module
   path and a library path can print alike, and the constant [g] of a
   module [Q] of the library [R.P] prints [R.P.Q.g], the name of the
   constant [g] of the library [R.P.Q]. An axiom constant the solution's
   proof reaches is the challenge's declaration when either
   - its module path, followed through every [MPdot] to its [MPfile], is
     rooted at a library that is one file for both sides ([one_file]), under
     whose [MPfile] no solution file the run reads can add a constant. The
     constant may be a field of a sealed module that the library does not
     export: the closure walk reaches it through the implementation, where
     no environment lookup sees it, and it is still the library's own; or
   - both the challenge environment and the solution environment declare
     the same kernel name (the challenge's own files, which the declaration
     comparison holds the solution to, and the libraries both sides read
     from one file). These lookups see only exported fields. Requiring the
     solution's to export it keeps the constant under that comparison: a
     solution that seals a challenge module, hides its axiom and gives it
     another type is refused. An axiom hidden inside a sealed module of a
     challenge file is refused even when the challenge hides it too:
     fail-closed, since the comparison does not see such a field.
   A forged constant declared in a changed file has a module path rooted
   at that file, which lies under a root the challenge stands in for, so
   its kernel name is neither under a one-file [MPfile] nor one the
   challenge declares.
   The same rule, on the inductive block's kernel name, decides whether a
   tolerated flag's object is the challenge's own. An axiom that is no
   constant is reached only when no library declares it, so the verdict
   counts it as no declaration of the challenge's without asking this
   rule. *)
let challenge_declares t ~challenge_env ~solution_env = function
  | GlobRef.ConstRef c ->
    rooted_one_file t (Constant.modpath c)
    || (Environ.mem_constant c challenge_env && Environ.mem_constant c solution_env)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    rooted_one_file t (MutInd.modpath mind)
    || (Environ.mem_mind mind challenge_env && Environ.mem_mind mind solution_env)
  | GlobRef.VarRef _ -> false

(* Why [challenge_declares] refused [obj], for the refusal's text. *)
let why_not_challenge ~challenge_env ~solution_env obj =
  let ch, sol = match obj with
    | GlobRef.ConstRef c -> Environ.mem_constant c challenge_env, Environ.mem_constant c solution_env
    | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
      Environ.mem_mind mind challenge_env, Environ.mem_mind mind solution_env
    | GlobRef.VarRef _ -> false, false
  in
  let why =
    match obj with
    | GlobRef.VarRef _ -> "a section variable is no declaration of the challenge's"
    | _ ->
      if ch && not sol then
        "the challenge declares it but the solution does not export it, and it lies under \
         no pre-checked or shared library"
      else
        "the challenge does not declare it (or hides it in a sealed module), and it lies \
         under no pre-checked or shared library"
  in
  "the proof reaches " ^ describe_object obj ^ ": " ^ why

(* What the verdict of every theorem reads besides the theorem's own
   closure. *)
type global_checks = {
  failures : failure list;  (** in the order [compare_declarations] finds them *)
  universes : universe_check;
  qualities : string option;  (** why [check_elim_constraints] fails *)
  rewrite_rule : Constant.t option;  (** a rule the config does not allow *)
}

type verdict = Pass | Fail of string

(* A theorem's entry in the verdict file. *)
type record = {
  r_name : string;
  r_verdict : verdict;
  r_axioms : string list;  (** printed names, sorted, each once *)
  r_flags : (string * string) list;  (** (kind, printed object) *)
}

(* The record of the theorem [th] of the config, [ch_constant] being the
   challenge's constant of that name. The theorem a verdict reads is the
   solution's constant of the challenge theorem's kernel name, not
   whichever solution constant prints its name: a module Q of the library
   R.P holding a constant thm prints R.P.Q.thm, the name of the theorem thm
   of the library R.P.Q. When the solution holds both, the theorem fails as
   declared twice under one name; when it lacks the theorem's kernel name,
   it fails as missing (the declaration comparison, which matches by kernel
   name too, says the same). Either way the verdict's axioms and flags are
   the kernel-name constant's, never the other's: the solution's
   environment and the closure read a constant by its user name.
   [sol_index] is the solution's [constant_index]. *)
let theorem_record t ~challenge_env ~solution_env ~sol_index st g (th, ch_constant) =
  let permitted = match th.th_axioms with
    | Some l -> l
    | None -> t.cfg.cfg_axioms
  in
  let printing = Option.default [] (CString.Map.find_opt th.th_name sol_index) in
  if not (Environ.mem_constant ch_constant solution_env) then
    { r_name = th.th_name; r_verdict = Fail "missing"; r_axioms = []; r_flags = [] }
  else
    let axioms, flags = Check_closure.axioms_and_flags st ch_constant in
    let permitted_axioms, bad_axioms =
      List.partition (fun (a, _) -> List.mem a permitted) axioms
    in
    (* A permitted name the proof reaches through an object the challenge
       did not declare: a forgery of that name. *)
    let forged_axioms =
      List.filter (fun (_, obj) ->
          not (match obj with
              | GlobRef.ConstRef _ -> challenge_declares t ~challenge_env ~solution_env obj
              | GlobRef.IndRef _ | GlobRef.ConstructRef _ | GlobRef.VarRef _ -> false))
        permitted_axioms
    in
    (* A config entry tolerates a flag when it names the same kind and
       either no object at all, or the flag's object by the name it prints
       AND that object is the challenge's own declaration of that name, by
       the rule for permitted axioms ([challenge_declares]). *)
    let names_it (kind, printed, _) (k, o) =
      String.equal k kind && (match o with None -> true | Some o -> String.equal o printed)
    in
    let tolerated ((_, _, obj) as f) =
      List.exists (fun ((_, o) as entry) ->
          names_it f entry
          && (match o with
              | None -> true
              | Some _ -> challenge_declares t ~challenge_env ~solution_env obj))
        t.cfg.cfg_flags
    in
    let bad_flags = List.filter (fun f -> not (tolerated f)) flags in
    (* A challenge declaration the solution changed is a changed challenge,
       whichever theorem names it: the statements are written against those
       definitions, so no theorem of the run can pass. The theorem's own
       record names its own difference when it has one. *)
    let reason =
      List.find_map (fun reason -> reason ()) [
        (fun () ->
           if List.length printing > 1 then
             let objs =
               List.sort String.compare
                 (List.map (fun c -> describe_object (GlobRef.ConstRef c)) printing)
             in
             Some ("the solution declares " ^ string_of_int (List.length printing) ^
                   " constants that print the theorem's name: " ^
                   String.concat " and " objs)
           else None);
        (* the reason of the last failure found under the theorem's name *)
        (fun () ->
           List.fold_left (fun r f -> if String.equal f.f_name th.th_name then Some f.f_reason else r)
             None g.failures);
        (fun () -> match g.failures with
           | f :: _ ->
             Some ("the challenge declaration " ^ f.f_name ^ " differs: " ^ f.f_reason)
           | [] -> None);
        (* A failing graph comparison fails every theorem, the universe one
           first. *)
        (fun () -> match g.universes with
           | Fails r -> Some r
           | Holds | Tolerated _ -> g.qualities);
        (fun () ->
           Option.map (fun c ->
               "the solution declares a rewrite rule on " ^ Constant.to_string c)
             g.rewrite_rule);
        (fun () -> match bad_axioms with
           | (a, _) :: _ -> Some ("the axiom " ^ a ^ " is not permitted")
           | [] -> None);
        (fun () -> match forged_axioms with
           | (a, obj) :: _ ->
             Some ("the axiom " ^ a ^ " is not the challenge's declaration of that \
                    name: " ^ why_not_challenge ~challenge_env ~solution_env obj)
           | [] -> None);
        (fun () -> match bad_flags with
           | ((k, o, obj) as f) :: _ ->
             let by_name =
               List.exists (fun ((_, e) as entry) -> Option.has_some e && names_it f entry)
                 t.cfg.cfg_flags
             in
             Some ("the relaxed typing flag " ^ k ^ " on " ^ o ^ " is not tolerated" ^
                   if by_name then
                     ": the config tolerates it on that name, but " ^ o ^
                     " is not the challenge's declaration of that name: " ^
                     why_not_challenge ~challenge_env ~solution_env obj
                   else "")
           | [] -> None);
      ]
    in
    (* Each (kind, printed object) once, in the order of [flags] (sorted),
       after the universe constraints a tolerance skipped, which no closure
       flag names. *)
    let printed =
      List.fold_right (fun (k, o, _) acc ->
          match acc with
          | (k', o') :: _ when String.equal k k' && String.equal o o' -> acc
          | _ -> (k, o) :: acc)
        flags []
    in
    let printed = match g.universes with
      | Tolerated constraints -> (universe_constraints_flag, constraints) :: printed
      | Holds | Fails _ -> printed
    in
    { r_name = th.th_name;
      r_verdict = (match reason with Some r -> Fail r | None -> Pass);
      r_axioms = CString.Set.elements (CString.Set.of_list (List.map fst axioms));
      r_flags = printed }

let record_json r =
  let verdict, reason = match r.r_verdict with
    | Pass -> "pass", ""
    | Fail reason -> "fail", reason
  in
  Json.Obj [
    "name", Json.Str r.r_name;
    "verdict", Json.Str verdict;
    "reason", Json.Str reason;
    "axioms", Json.List (List.map (fun a -> Json.Str a) r.r_axioms);
    "flags", Json.List (List.map (fun (k, o) -> Json.Obj ["kind", Json.Str k;
                                                          "object", Json.Str o]) r.r_flags);
  ]

(* The verdict goes to a temporary file in the directory of [out], which is
   then renamed over it, so a write that fails (a full disk, say) leaves no
   part of a verdict where a reader would take it for a whole one: the
   temporary file is removed and the run exits non-zero. *)
let write_verdict out text =
  let tmp, ch =
    Filename.open_temp_file ~perms:0o666 ~temp_dir:(Filename.dirname out)
      (Filename.basename out) ".tmp"
  in
  try
    output_string ch text;
    output_char ch '\n';
    close_out ch;
    Sys.rename tmp out
  with e ->
    let e = Exninfo.capture e in
    close_out_noerr ch;
    (try Sys.remove tmp with Sys_error _ -> ());
    Exninfo.iraise e

(* A root bound to one of the top-level names of the default load path (the
   corelib directory, user-contrib, the XDG directories and ROCQPATH), or to
   the empty root, which binds every name, puts the solution's directory
   where a library of the default load path is looked up: the two sides
   would read different files under one name, and the one the solution
   wrote would decide. No config can make that safe, and a run needs one
   bound root only, the solution's own. *)
let check_roots ~default_roots roots =
  List.iter (fun (unix_path, rocq_root) ->
      match List.rev (DirPath.repr rocq_root) with
      | [] ->
        CErrors.user_err
          Pp.(str ("The directory " ^ unix_path ^ " is bound to the empty root, which binds \
                    every library name the default load path serves. A -compare run \
                    refuses it."))
      | id :: _ ->
        if List.mem_f Id.equal id default_roots then
          CErrors.user_err
            Pp.(str ("The directory " ^ unix_path ^ " is bound to " ^
                     DirPath.to_string rocq_root ^ ", a name the default load path \
                     serves. A -compare run refuses it: the two sides would read \
                     different files under one library name.")))
    roots

(* The challenge stands in for the bound root that the libraries named for
   checking live under, and the challenge directory holds one root's tree:
   [add_load_path] binds a directory to one logical root at a time, so a
   second root would take the binding of the first, and with no root every
   library would count as a shared one, read from one file for both sides.
   A root that only a pre-checked library or another shared tree uses is
   left alone, since the challenge directory does not hold it. Every other
   bound root is an open root ([check_open_roots]). *)
let run cfg ~dir ~out ~roots ~trusted ~checked ~admitted ~add_load_path env senv0 =
  let substitutes root = List.exists (CheckLibrary.under_root ~root) checked in
  let challenge_root =
    match List.sort_uniquize DirPath.compare (List.filter substitutes (List.map snd roots)) with
    | [root] -> root
    | [] ->
      CErrors.user_err
        Pp.(str "The libraries named for checking lie under no root that -Q or -R binds. \
                 The challenge directory stands in for one root, the solution's project \
                 root, which -Q binds. A -compare run refuses them.")
    | _ :: _ :: _ as l ->
      CErrors.user_err
        Pp.(str ("The libraries named for checking lie under more than one root that -Q \
                  or -R binds: " ^ String.concat ", " (List.map DirPath.to_string l) ^
                 ". The challenge directory stands in for one root, the solution's \
                  project root. A -compare run refuses them."))
  in
  let open_roots =
    List.filter_map (fun (unix_path, rocq_root) ->
        if substitutes rocq_root then None else Some (rocq_root, unix_path))
      roots
  in
  let t =
    prepare cfg ~dir ~challenge_root ~open_roots ~bound_dirs:(List.map fst roots) ~trusted
      ~admitted
  in
  let challenge_env, challenge_libs = load_challenge t ~add_load_path senv0 in
  (* A pre-checked library, and each library it rests on that is one file
     for both sides ([prechecked_closure]), is not compared: their
     declarations are equal by construction, and walking them would read
     the whole standard library on every run. Every other library of the
     challenge files' closure is. *)
  let skip = DirPath.Set.filter (one_file t) t.prechecked_closure in
  let libs = DirPath.Set.diff challenge_libs skip in
  let ch_index = constant_index challenge_env in
  (* A theorem the challenge does not state, or states twice under one
     printed name, is a config error, not a verdict. *)
  let ch_theorem th =
    match CString.Map.find_opt th.th_name ch_index with
    | None | Some [] ->
      CErrors.user_err
        Pp.(str ("The config names the theorem " ^ th.th_name ^
                 ", which the challenge does not hold."))
    | Some [c] -> c
    | Some (_ :: _ :: _) ->
      CErrors.user_err
        Pp.(str ("The config names the theorem " ^ th.th_name ^
                 ", a name that two constants of the challenge print."))
  in
  let named = List.map (fun th -> th, ch_theorem th) t.cfg.cfg_theorems in
  let theorems =
    List.fold_left (fun acc th -> CString.Set.add th.th_name acc) CString.Set.empty
      t.cfg.cfg_theorems
  in
  let failures, m = compare_declarations t ~challenge_env ~solution_env:env ~libs ~theorems in
  let universes = check_constraints t ~challenge_env ~solution_env:env m in
  let qualities = check_elim_constraints ~challenge_env ~solution_env:env m in
  let sol_index = constant_index env in
  (* Every library the solution loaded is the solution's own concern, a
     library only the solution has included, which the declaration
     comparison does not visit. The exceptions are the libraries that are
     one file for both sides ([one_file]), which may carry rules the
     challenge did not write. *)
  let rewrite_rule =
    if t.cfg.cfg_rewrite_rules then None
    else solution_rewrite_rule env (List.filter (fun dp -> not (one_file t dp)) t.solution_libs)
  in
  let g = { failures; universes; qualities; rewrite_rule } in
  let st = Check_closure.closure_state env CheckLibrary.indirect_accessor in
  let records =
    List.map (theorem_record t ~challenge_env ~solution_env:env ~sol_index st g) named
  in
  let decls =
    List.map (fun f -> Json.Obj ["name", Json.Str f.f_name; "reason", Json.Str f.f_reason])
      failures
    @ (match universes with
       | Fails u -> [Json.Obj ["name", Json.Str "<universes>"; "reason", Json.Str u]]
       | Holds | Tolerated _ -> [])
    @ (match qualities with
       | None -> []
       | Some q -> [Json.Obj ["name", Json.Str "<qualities>"; "reason", Json.Str q]])
  in
  (* The libraries given with -admit, in the order given and each once: the
     run trusts them unchecked, and no digest pins them. *)
  let admitted = List.uniquize (List.map DirPath.to_string admitted) in
  write_verdict out (Json.to_string (Json.Obj [
      "format", Json.Int 1;
      "theorems", Json.List (List.map record_json records);
      "declarations", Json.List decls;
      "admitted", Json.List (List.map (fun a -> Json.Str a) admitted);
    ]))
