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

    The challenge is a set of [.vo] files that setup compiled and checked, and
    the answer is the tree the agent handed back, compiled at the same paths
    and under the same library names. [rocqchk] checks the answer with the
    kernel as it does today; this module loads the challenge into a second
    environment without a check, compares every challenge declaration with the
    answer declaration of the same kernel name, computes each named theorem's
    axiom closure, and writes a JSON verdict.

    The comparison is structural: two declarations are equal when their terms
    are the same after a one-to-one renaming of universe levels. There is no
    conversion and no reduction, and no constant is unfolded. *)

open Util
open Names
open Declarations

(************************************************************************)
(** {6 SHA-256}

    The checker links only [boot] and [kernel], so there is no digest library
    to call. This is FIPS 180-4's SHA-256, tested against the standard vectors
    in test-suite/misc/compare.sh (case [sha256]), which also compares it with
    [sha256sum] on every file the suite builds. *)

module Sha256 : sig
  val hex_of_string : string -> string
  val hex_of_file : string -> string
end = struct

  let k = [|
    0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5;
    0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
    0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3;
    0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
    0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc;
    0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
    0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7;
    0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
    0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13;
    0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
    0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3;
    0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
    0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5;
    0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
    0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208;
    0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 |]

  let mask = 0xffffffff
  let rotr x n = ((x lsr n) lor (x lsl (32 - n))) land mask

  type t = {
    h : int array;
    buf : Bytes.t;        (* a partial block, [len] bytes of it *)
    mutable len : int;
    mutable total : int;  (* bytes fed so far *)
    w : int array;
  }

  let create () = {
    h = [| 0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a;
           0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19 |];
    buf = Bytes.create 64;
    len = 0;
    total = 0;
    w = Array.make 64 0;
  }

  let block st b off =
    let w = st.w in
    for i = 0 to 15 do
      let j = off + 4 * i in
      w.(i) <-
        (Char.code (Bytes.get b j) lsl 24)
        lor (Char.code (Bytes.get b (j + 1)) lsl 16)
        lor (Char.code (Bytes.get b (j + 2)) lsl 8)
        lor Char.code (Bytes.get b (j + 3))
    done;
    for i = 16 to 63 do
      let x = w.(i - 15) and y = w.(i - 2) in
      let s0 = rotr x 7 lxor rotr x 18 lxor (x lsr 3) in
      let s1 = rotr y 17 lxor rotr y 19 lxor (y lsr 10) in
      w.(i) <- (w.(i - 16) + s0 + w.(i - 7) + s1) land mask
    done;
    let a = ref st.h.(0) and b1 = ref st.h.(1) and c = ref st.h.(2) and d = ref st.h.(3) in
    let e = ref st.h.(4) and f = ref st.h.(5) and g = ref st.h.(6) and h = ref st.h.(7) in
    for i = 0 to 63 do
      let s1 = rotr !e 6 lxor rotr !e 11 lxor rotr !e 25 in
      let ch = (!e land !f) lxor (lnot !e land mask land !g) in
      let t1 = (!h + s1 + ch + k.(i) + w.(i)) land mask in
      let s0 = rotr !a 2 lxor rotr !a 13 lxor rotr !a 22 in
      let maj = (!a land !b1) lxor (!a land !c) lxor (!b1 land !c) in
      let t2 = (s0 + maj) land mask in
      h := !g; g := !f; f := !e; e := (!d + t1) land mask;
      d := !c; c := !b1; b1 := !a; a := (t1 + t2) land mask
    done;
    st.h.(0) <- (st.h.(0) + !a) land mask;
    st.h.(1) <- (st.h.(1) + !b1) land mask;
    st.h.(2) <- (st.h.(2) + !c) land mask;
    st.h.(3) <- (st.h.(3) + !d) land mask;
    st.h.(4) <- (st.h.(4) + !e) land mask;
    st.h.(5) <- (st.h.(5) + !f) land mask;
    st.h.(6) <- (st.h.(6) + !g) land mask;
    st.h.(7) <- (st.h.(7) + !h) land mask

  let feed st b off len =
    st.total <- st.total + len;
    let off = ref off and len = ref len in
    if st.len > 0 then begin
      let take = min (64 - st.len) !len in
      Bytes.blit b !off st.buf st.len take;
      st.len <- st.len + take;
      off := !off + take;
      len := !len - take;
      if st.len = 64 then (block st st.buf 0; st.len <- 0)
    end;
    while !len >= 64 do
      block st b !off;
      off := !off + 64;
      len := !len - 64
    done;
    if !len > 0 then begin
      Bytes.blit b !off st.buf 0 !len;
      st.len <- !len
    end

  let finish st =
    let bits = st.total * 8 in
    let pad = Bytes.make 72 '\000' in
    Bytes.set pad 0 '\x80';
    (* enough zero bytes to leave room for the 8-byte length at a block end *)
    let n = if st.len < 56 then 56 - st.len else 120 - st.len in
    for i = 0 to 7 do
      Bytes.set pad (n + i) (Char.chr ((bits lsr (8 * (7 - i))) land 0xff))
    done;
    feed st pad 0 (n + 8);
    let b = Buffer.create 64 in
    Array.iter (fun x -> Buffer.add_string b (Printf.sprintf "%08x" x)) st.h;
    Buffer.contents b

  let hex_of_string s =
    let st = create () in
    feed st (Bytes.of_string s) 0 (String.length s);
    finish st

  let hex_of_file f =
    let ch = try open_in_bin f with Sys_error e -> CErrors.user_err (Pp.str e) in
    Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
        let st = create () in
        let b = Bytes.create 65536 in
        let rec loop () =
          let n = input ch b 0 65536 in
          if n > 0 then (feed st b 0 n; loop ())
        in
        loop ();
        finish st)
end

let sha256_of_file = Sha256.hex_of_file

(************************************************************************)
(** {6 JSON}

    A reader and a writer, for the same reason: the checker links no JSON
    library. The reader is strict, because the config decides a grade: a
    duplicate key, a byte after the top-level value, a byte sequence that is
    not UTF-8, a control character in a string, a leading zero or a number
    that is not an integer are each an error. The writer escapes, so a
    constant name holding a line break stays one JSON string. *)

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
  let check_utf8 s =
    let n = String.length s in
    let byte i = Char.code s.[i] in
    let cont i = i < n && byte i land 0xc0 = 0x80 in
    let rec loop i =
      if i >= n then ()
      else
        let c = byte i in
        if c < 0x80 then loop (i + 1)
        else if c land 0xe0 = 0xc0 then
          if c < 0xc2 || not (cont (i + 1)) then error "invalid UTF-8"
          else loop (i + 2)
        else if c land 0xf0 = 0xe0 then
          if not (cont (i + 1) && cont (i + 2)) then error "invalid UTF-8"
          else
            let cp = ((c land 0x0f) lsl 12) lor ((byte (i + 1) land 0x3f) lsl 6)
                     lor (byte (i + 2) land 0x3f) in
            if cp < 0x800 || (cp >= 0xd800 && cp <= 0xdfff) then error "invalid UTF-8"
            else loop (i + 3)
        else if c land 0xf8 = 0xf0 then
          if not (cont (i + 1) && cont (i + 2) && cont (i + 3)) then error "invalid UTF-8"
          else
            let cp = ((c land 0x07) lsl 18) lor ((byte (i + 1) land 0x3f) lsl 12)
                     lor ((byte (i + 2) land 0x3f) lsl 6) lor (byte (i + 3) land 0x3f) in
            if cp < 0x10000 || cp > 0x10ffff then error "invalid UTF-8"
            else loop (i + 4)
        else error "invalid UTF-8"
    in
    loop 0

  let add_utf8 b cp =
    if cp < 0x80 then Buffer.add_char b (Char.chr cp)
    else if cp < 0x800 then begin
      Buffer.add_char b (Char.chr (0xc0 lor (cp lsr 6)));
      Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3f)))
    end else if cp < 0x10000 then begin
      Buffer.add_char b (Char.chr (0xe0 lor (cp lsr 12)));
      Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3f)));
      Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3f)))
    end else begin
      Buffer.add_char b (Char.chr (0xf0 lor (cp lsr 18)));
      Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 12) land 0x3f)));
      Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3f)));
      Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3f)))
    end

  let parse s =
    check_utf8 s;
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
                add_utf8 b cp
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
      let l = String.length lit in
      if !pos + l <= n && String.sub s !pos l = lit then (pos := !pos + l; v)
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

  (* The writer. Every byte above 127 is written as a \u escape of the code
     point it starts, and a byte that is not part of a valid UTF-8 sequence as
     U+FFFD, so the output is valid JSON whatever a name holds. *)
  let escape b s =
    let n = String.length s in
    let byte i = Char.code s.[i] in
    let cont i = i < n && byte i land 0xc0 = 0x80 in
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
        let c = byte i in
        if c = Char.code '"' then (Buffer.add_string b "\\\""; loop (i + 1))
        else if c = Char.code '\\' then (Buffer.add_string b "\\\\"; loop (i + 1))
        else if c = 8 then (Buffer.add_string b "\\b"; loop (i + 1))
        else if c = 12 then (Buffer.add_string b "\\f"; loop (i + 1))
        else if c = 10 then (Buffer.add_string b "\\n"; loop (i + 1))
        else if c = 13 then (Buffer.add_string b "\\r"; loop (i + 1))
        else if c = 9 then (Buffer.add_string b "\\t"; loop (i + 1))
        else if c < 0x20 || c = 0x7f then (unicode c; loop (i + 1))
        else if c < 0x80 then (Buffer.add_char b s.[i]; loop (i + 1))
        else if c land 0xe0 = 0xc0 && c >= 0xc2 && cont (i + 1) then
          (unicode (((c land 0x1f) lsl 6) lor (byte (i + 1) land 0x3f)); loop (i + 2))
        else if c land 0xf0 = 0xe0 && cont (i + 1) && cont (i + 2) then
          (unicode (((c land 0x0f) lsl 12) lor ((byte (i + 1) land 0x3f) lsl 6)
                    lor (byte (i + 2) land 0x3f));
           loop (i + 3))
        else if c land 0xf8 = 0xf0 && cont (i + 1) && cont (i + 2) && cont (i + 3) then
          (unicode (((c land 0x07) lsl 18) lor ((byte (i + 1) land 0x3f) lsl 12)
                    lor ((byte (i + 2) land 0x3f) lsl 6) lor (byte (i + 3) land 0x3f));
           loop (i + 4))
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

type prechecked = { pc_library : string; pc_sha256 : string }

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

let answer_universe_constraints = "answer-universe-constraints"

(* A pre-checked library loads through the existing -admit path: the option
   adds it to the admit list, so the config is the only place that names it. *)
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
  (* A config that names no theorem grades nothing, and a name twice over
     would write two records a reader cannot tell apart. *)
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
  (* A tolerated flag names the kind, and may name the object it is
     tolerated on. With an object, a relaxed condition the standard library
     rests on does not tolerate the same condition in the agent's own
     declaration.

     Without an object, [indices-not-mattering] tolerates the kind wherever
     it appears: every inductive of an image built without [-indices-matter]
     may carry it, and the route this comparator replaces always allows it.
     [uip] is allowed by the route this comparator replaces when the task
     enables [allow_uip]; this comparator accepts a kind-only [uip] entry
     when its config requests one. [answer-universe-constraints] is also
     kind-only, but has a narrower meaning: it skips only the
     answer-to-challenge universe comparison. It names no declaration, so an
     object would not make the requested relaxation more precise.

     The rest -- [assumed-positive], [unsafe-fixpoint], [type-in-type],
     [unchecked-eliminations] -- are how a proof of False is written, and
     the replaced route denies them by name or vouches for one object at a
     time, so a kind-only entry for them is refused here rather than left to
     a config to get right. *)
  let kind_only_allowed =
    ["indices-not-mattering"; "uip"; answer_universe_constraints]
  in
  let flags = match get top "tolerated_flags" with
    | None -> []
    | Some v ->
      List.map (fun e ->
          let e = as_obj "a tolerated flag" e in
          fields "a tolerated flag" ["kind"; "object"] e;
          match get e "kind", get e "object" with
          | Some k, Some o ->
            let k = as_string "a tolerated flag's kind" k in
            if String.equal k answer_universe_constraints then
              cfg_error ("the tolerated flag " ^ answer_universe_constraints ^
                         " does not name an object");
            k, Some (as_string "a tolerated flag's object" o)
          | Some k, None ->
            let k = as_string "a tolerated flag's kind" k in
            if not (List.exists (String.equal k) kind_only_allowed) then
              cfg_error ("the tolerated flag " ^ k ^ " needs an object: only " ^
                         "indices-not-mattering and uip tolerate every object; " ^
                         answer_universe_constraints ^ " is a global check");
            k, None
          | None, _ -> cfg_error "a tolerated flag needs a kind")
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
            { pc_library = as_string "a prechecked library" l;
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
(** {6 The universe level map}

    One map for the whole run, a bijection between the challenge's
    monomorphic levels and the answer's. It is seeded with the identity on
    every level of a SHARED library -- one outside the roots the challenge
    stands in for, which is one file for both sides -- and on every
    pre-checked library's, so that a constraint between a level of the
    challenge's own and one of those is a constraint between two mapped
    levels, which the constraint check below sees. Without the seed a level
    no compared term names is not in the map at all, and a constraint
    reaching it is passed over: an opaque body is never compared, so a
    challenge proof's own constraint on such a level would be lost. The
    rest of the map is built while the declarations are compared.

    A level of a polymorphic context is a [Level.var], bound by position, so
    it is compared by its index and never enters the map. *)

type umap = {
  fwd : Univ.Level.t Univ.Level.Map.t;  (** challenge to answer *)
  bwd : Univ.Level.t Univ.Level.Map.t;  (** answer to challenge *)
}

let empty_umap = { fwd = Univ.Level.Map.empty; bwd = Univ.Level.Map.empty }

type diff = string

exception Diff of diff

let diff fmt = Printf.ksprintf (fun s -> raise (Diff s)) fmt

(* A universe whose levels no comparison so far has mapped, and that one
   pass cannot map alone (two entries of one increment). The declaration is
   compared again once the others have been, since a later declaration --
   the one that introduced those levels -- may map them. *)
exception Undecided of diff

let level_name u = Univ.Level.to_string u

let add_level m u v =
  { fwd = Univ.Level.Map.add u v m.fwd; bwd = Univ.Level.Map.add v u m.bwd }

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
          diff "universe %s is already the image of %s, so %s cannot map to it"
            (level_name v) (level_name u') (level_name u)
        | None -> add_level m u v

(* A universe is a maximum of levels raised by a constant. Entries whose level
   the map already fixes are matched by that level; the rest are matched by
   their increment, in order. *)
let map_universe m u v =
  let lu = Univ.Universe.repr u and lv = Univ.Universe.repr v in
  if List.length lu <> List.length lv then
    diff "universe %s against %s"
      (Pp.string_of_ppcmds (Univ.Universe.raw_pr u))
      (Pp.string_of_ppcmds (Univ.Universe.raw_pr v));
  let m = ref m in
  let rest = ref lv in
  let fresh = ref [] in
  let take_level target n =
    let rec go seen = function
      | [] ->
        diff "universe %s has no %s+%d" (Pp.string_of_ppcmds (Univ.Universe.raw_pr v))
          (level_name target) n
      | (l2, n2) :: tl when Univ.Level.equal l2 target && Int.equal n2 n ->
        List.rev_append seen tl
      | e :: tl -> go (e :: seen) tl
    in
    rest := go [] !rest
  in
  List.iter (fun (l, n) ->
      match Univ.Level.var_index l, Univ.Level.name l with
      (* a level of a polymorphic context, or Set: it stands for itself *)
      | Some _, _ | None, None -> take_level l n
      | None, Some _ ->
        match Univ.Level.Map.find_opt l !m.fwd with
        | None -> fresh := (l, n) :: !fresh
        | Some l' -> take_level l' n)
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
        diff "universe %s against %s"
          (Pp.string_of_ppcmds (Univ.Universe.raw_pr u))
          (Pp.string_of_ppcmds (Univ.Universe.raw_pr v));
      let decided = ref false in
      let keep = ref [] in
      List.iter (fun (l, n) ->
          match Univ.Level.Map.find_opt l !m.fwd with
          | Some l' ->
            (* mapped since this entry was set aside: match it by level *)
            let rec take seen = function
              | [] ->
                diff "universe %s has no %s+%d"
                  (Pp.string_of_ppcmds (Univ.Universe.raw_pr v)) (level_name l') n
              | (l2, n2) :: tl when Univ.Level.equal l2 l' && Int.equal n2 n ->
                List.rev_append seen tl
              | e :: tl -> take (e :: seen) tl
            in
            rest := take [] !rest;
            decided := true
          | None ->
            match List.filter (fun (_, n2) -> Int.equal n n2) !rest with
            | [ (l2, _) ] ->
              m := map_level !m l l2;
              rest := List.filter (fun (l3, n3) ->
                  not (Univ.Level.equal l3 l2 && Int.equal n3 n)) !rest;
              decided := true
            | [] ->
              diff "universe %s has no entry of increment %d"
                (Pp.string_of_ppcmds (Univ.Universe.raw_pr v)) n
            | _ :: _ :: _ -> keep := (l, n) :: !keep)
        !fresh;
      let left = List.rev !keep in
      if not !decided then
        raise (Undecided (Printf.sprintf
          "universe %s against %s: which level of the answer each level of the \
           challenge stands for is not decided"
          (Pp.string_of_ppcmds (Univ.Universe.raw_pr u))
          (Pp.string_of_ppcmds (Univ.Universe.raw_pr v))));
      fresh := left;
      passes ()
    end
  in
  passes ();
  !m

let map_quality q1 q2 =
  if not (Sorts.Quality.equal q1 q2) then diff "sort quality"

let map_sort m s1 s2 =
  let open Sorts in
  match s1, s2 with
  | SProp, SProp | Prop, Prop | Set, Set -> m
  | Type u, Type v -> map_universe m u v
  | QSort (q1, u), QSort (q2, v) ->
    if not (QVar.equal q1 q2) then diff "sort variable";
    map_universe m u v
  | (SProp | Prop | Set | Type _ | QSort _), _ -> diff "sort"

let map_instance m i1 i2 =
  let q1, u1 = UVars.Instance.to_array i1 and q2, u2 = UVars.Instance.to_array i2 in
  if Array.length q1 <> Array.length q2 || Array.length u1 <> Array.length u2 then
    diff "universe instance";
  Array.iter2 map_quality q1 q2;
  Array.fold_left2 map_level m u1 u2

let map_relevance r1 r2 =
  if not (Sorts.relevance_equal r1 r2) then diff "relevance"

let map_annot a1 a2 =
  map_relevance a1.Context.binder_relevance a2.Context.binder_relevance

(************************************************************************)
(** {6 Structural equality of terms}

    No conversion, no reduction, and no constant is unfolded: two terms are
    equal when they have the same shape, the same kernel names and universes
    the map pairs. Binder names are not compared, their relevance is. A
    [Cast] is a type ascription the kernel has already used, so it is
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
    if not (Constant.CanOrd.equal c1 c2) then
      diff "constant %s against %s" (Constant.to_string c1) (Constant.to_string c2);
    map_instance m u1 u2
  | Ind ((i1, n1), u1), Ind ((i2, n2), u2) ->
    if not (MutInd.CanOrd.equal i1 i2 && Int.equal n1 n2) then
      diff "inductive %s against %s" (MutInd.to_string i1) (MutInd.to_string i2);
    map_instance m u1 u2
  | Construct (((i1, n1), k1), u1), Construct (((i2, n2), k2), u2) ->
    if not (MutInd.CanOrd.equal i1 i2 && Int.equal n1 n2 && Int.equal k1 k2) then
      diff "constructor of %s against %s" (MutInd.to_string i1) (MutInd.to_string i2);
    map_instance m u1 u2
  | Case (ci1, u1, pms1, p1, iv1, s1, br1), Case (ci2, u2, pms2, p2, iv2, s2, br2) ->
    let (m1, n1) = ci1.ci_ind and (m2, n2) = ci2.ci_ind in
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

(** The shape the kernel's own comparison will take when [Indmerge] lands. *)
let equal_constr m c1 c2 =
  match eq_constr m c1 c2 with
  | m -> Ok m
  | exception (Diff d | Undecided d) -> Error d

(************************************************************************)
(** {6 Declarations} *)

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

let eq_universes m u1 u2 = match u1, u2 with
  | Monomorphic, Monomorphic -> m
  | Polymorphic a1, Polymorphic a2 ->
    if UVars.AbstractContext.size a1 <> UVars.AbstractContext.size a2 then
      diff "the universe context has another size";
    let (e1, c1) = UVars.UContext.constraints (UVars.AbstractContext.repr a1) in
    let (e2, c2) = UVars.UContext.constraints (UVars.AbstractContext.repr a2) in
    if not (Univ.UnivConstraints.equal c1 c2 && Sorts.ElimConstraints.equal e1 e2) then
      diff "the universe context has other constraints";
    m
  | Monomorphic, Polymorphic _ -> diff "a monomorphic declaration is polymorphic in the answer"
  | Polymorphic _, Monomorphic -> diff "a polymorphic declaration is monomorphic in the answer"

(* What the challenge leaves without a body, the answer may fill only when
   that is the task: a proof. [Admitted], [Axiom] and [Parameter] give the
   same .vo content, so the kind of the declaration cannot tell them apart;
   its type can. A constant whose type is a proposition is a lemma, and
   proving it is the whole point. A constant whose type is data -- an
   [open definition], which the spec lists as a non-goal -- must stay
   without a body, or the answer could choose the function the statements
   are about. A theorem the config names is a proof whatever its sort.

   The sort is the one the answer environment gives the answer's own type,
   which R2 has already found equal to the challenge's. A type the answer
   environment cannot type is treated as data: the kernel check of the
   answer would have refused it. *)
let is_proposition env (cb : constant_body) =
  let env = match cb.const_universes with
    | Monomorphic -> env
    | Polymorphic ctx ->
      Environ.push_context ~strict:false (UVars.AbstractContext.repr ctx) env
  in
  match Typeops.infer_type env cb.const_type with
  | j ->
    (match j.Environ.utj_type with
     | Sorts.Prop | Sorts.SProp -> true
     | Sorts.Set | Sorts.Type _ | Sorts.QSort _ -> false)
  | exception e when CErrors.noncritical e -> false

let eq_const_body ~env ~is_theorem m (cb1 : constant_body) (cb2 : constant_body) =
  map_relevance cb1.const_relevance cb2.const_relevance;
  let m = eq_universes m cb1.const_universes cb2.const_universes in
  let m = eq_constr m cb1.const_type cb2.const_type in
  match cb1.const_body, cb2.const_body with
  | Undef _, Undef _ -> m
  | Undef _, (Def _ | OpaqueDef _) ->
    if is_theorem || is_proposition env cb2 then m
    else diff "the challenge leaves this declaration open and the answer defines it"
  | Undef _, _ -> diff "an assumption is a primitive or a symbol in the answer"
  (* An opaque body is never compared, but a proof stays a proof: a Qed in
     the challenge may not become a transparent definition, which would let
     the answer's body reach conversion where the challenge's could not. *)
  | OpaqueDef _, OpaqueDef _ -> m
  | Def b1, Def b2 -> eq_constr m b1 b2
  | Def _, OpaqueDef _ -> diff "a transparent definition is opaque in the answer"
  | Def _, _ -> diff "a transparent definition is not a definition in the answer"
  | OpaqueDef _, _ -> diff "an opaque proof is not an opaque proof in the answer"
  | Primitive p1, Primitive p2 ->
    if not (CPrimitives.equal p1 p2) then diff "another primitive"; m
  | Primitive _, _ -> diff "a primitive is not a primitive in the answer"
  | Symbol _, Symbol _ -> m
  | Symbol _, _ -> diff "a symbol is not a symbol in the answer"

let eq_record m r1 r2 = match r1, r2 with
  | NotRecord, NotRecord | FakeRecord, FakeRecord -> m
  | PrimRecord p1, PrimRecord p2 ->
    if not (Id.equal p1.id p2.id) then diff "the record binder name";
    if not (Array.equal Id.equal p1.projections p2.projections) then diff "the projections";
    if not (Array.equal Sorts.relevance_equal p1.relevances p2.relevances) then
      diff "a projection's relevance";
    if p1.has_eta <> p2.has_eta then diff "the record's eta";
    if not (Int.equal (Array.length p1.tys) (Array.length p2.tys)) then diff "the projections";
    Array.fold_left2 eq_constr m p1.tys p2.tys
  | (NotRecord | FakeRecord | PrimRecord _), _ -> diff "the record kind"

let eq_variance v1 v2 = match v1, v2 with
  | None, None -> ()
  | Some (a1, b1), Some (a2, b2) ->
    if not (Array.equal (fun x y -> x = y) a1 a2 && Array.equal (fun x y -> x = y) b1 b2) then
      diff "the universe variance"
  | None, Some _ | Some _, None -> diff "the universe variance"

(* The relaxed kernel conditions a declaration was typed under are part of
   what it claims. The conversion oracle and the performance switches are
   not: they change how the kernel works, not what it accepted. *)
let eq_typing_flags (f1 : typing_flags) (f2 : typing_flags) =
  if f1.check_guarded <> f2.check_guarded
  || f1.check_positive <> f2.check_positive
  || f1.check_universes <> f2.check_universes
  || f1.check_eliminations <> f2.check_eliminations
  || f1.indices_matter <> f2.indices_matter
  || f1.impredicative_set <> f2.impredicative_set
  then diff "the kernel conditions the declaration was typed under"

let eq_one_ind m (mip1 : one_inductive_body) (mip2 : one_inductive_body) =
  if not (Id.equal mip1.mind_typename mip2.mind_typename) then diff "the type's name";
  map_relevance mip1.mind_relevance mip2.mind_relevance;
  let m = eq_rel_context m mip1.mind_arity_ctxt mip2.mind_arity_ctxt in
  let m = eq_constr m mip1.mind_user_arity mip2.mind_user_arity in
  let m = map_sort m mip1.mind_sort mip2.mind_sort in
  if not (Int.equal mip1.mind_nrealargs mip2.mind_nrealargs) then diff "the number of indices";
  if (match mip1.mind_squashed, mip2.mind_squashed with
      | None, None -> false
      | Some AlwaysSquashed, Some AlwaysSquashed -> false
      | Some (SometimesSquashed q1), Some (SometimesSquashed q2) ->
        not (Sorts.Quality.Set.equal q1 q2)
      | _ -> true)
  then diff "the elimination restriction";
  if not (Array.equal Id.equal mip1.mind_consnames mip2.mind_consnames) then
    diff "the constructor names";
  if not (Int.equal (Array.length mip1.mind_user_lc) (Array.length mip2.mind_user_lc)) then
    diff "the number of constructors";
  let m = Array.fold_left2 eq_constr m mip1.mind_user_lc mip2.mind_user_lc in
  eq_record m mip1.mind_record mip2.mind_record

let eq_mib_body m (mib1 : mutual_inductive_body) (mib2 : mutual_inductive_body) =
  if mib1.mind_finite <> mib2.mind_finite then diff "the recursivity kind";
  if not (Int.equal mib1.mind_nparams mib2.mind_nparams) then diff "the number of parameters";
  if not (Int.equal mib1.mind_nparams_rec mib2.mind_nparams_rec) then
    diff "the number of uniform parameters";
  if mib1.mind_private <> mib2.mind_private then diff "the private flag";
  if Option.has_some mib1.mind_template <> Option.has_some mib2.mind_template then
    diff "a template-polymorphic inductive type is not template-polymorphic in the answer";
  eq_typing_flags mib1.mind_typing_flags mib2.mind_typing_flags;
  eq_variance mib1.mind_variance mib2.mind_variance;
  eq_variance mib1.mind_sec_variance mib2.mind_sec_variance;
  let m = eq_universes m mib1.mind_universes mib2.mind_universes in
  let m = eq_rel_context m mib1.mind_params_ctxt mib2.mind_params_ctxt in
  if not (Int.equal (Array.length mib1.mind_packets) (Array.length mib2.mind_packets)) then
    diff "the number of types in the block";
  Array.fold_left2 eq_one_ind m mib1.mind_packets mib2.mind_packets

(** The shape [Indmerge.eq_mib] will take. The environment is not read: the
    comparison is structural. *)
let eq_mib m _env mib1 mib2 =
  match eq_mib_body m mib1 mib2 with
  | m -> Ok m
  | exception (Diff d | Undecided d) -> Error d

(************************************************************************)
(** {6 Module types}

    A field of a [Module Type] is not a constant of the environment, so the
    walk over the environment's constants does not see it. Each challenge
    module type is compared with the answer's module type of the same path,
    field by field. *)

let rec eq_signature ~env m s1 s2 =
  match s1, s2 with
  | NoFunctor b1, NoFunctor b2 -> eq_structure ~env m b1 b2
  | MoreFunctor (_, t1, s1), MoreFunctor (_, t2, s2) ->
    eq_signature ~env (eq_modtype ~env m t1 t2) s1 s2
  | NoFunctor _, MoreFunctor _ -> diff "a module type is a functor in the answer"
  | MoreFunctor _, NoFunctor _ -> diff "a functor is not a functor in the answer"

and eq_structure ~env m b1 b2 =
  List.fold_left (fun m (l, f1) ->
      match List.assoc_opt l b2 with
      | None -> diff "the field %s is missing from the answer" (Id.to_string l)
      | Some f2 ->
        match f1, f2 with
        (* A field of a module type is never a config-named theorem: the
           config names a constant of the environment. *)
        | SFBconst c1, SFBconst c2 -> eq_const_body ~env ~is_theorem:false m c1 c2
        | SFBmind i1, SFBmind i2 -> eq_mib_body m i1 i2
        | SFBrules r1, SFBrules r2 ->
          (* The symbols the block rewrites must be the same ones, in the
             same order. The machine rules themselves are not compared: a
             rewrite rule reaches a verdict through the rewrite_rules
             switch of the config, which refuses every one of them unless
             the task permits them. *)
          let names b = List.map fst b.rewrules_rules in
          if not (CList.equal Constant.CanOrd.equal (names r1) (names r2)) then
            diff "the field %s rewrites other symbols in the answer" (Id.to_string l);
          m
        | SFBmodule mb1, SFBmodule mb2 ->
          eq_signature ~env m (Mod_declarations.mod_type mb1) (Mod_declarations.mod_type mb2)
        | SFBmodtype t1, SFBmodtype t2 -> eq_modtype ~env m t1 t2
        | (SFBconst _ | SFBmind _ | SFBrules _ | SFBmodule _ | SFBmodtype _), _ ->
          diff "the field %s is of another kind in the answer" (Id.to_string l))
    m b1

and eq_modtype ~env m t1 t2 =
  eq_signature ~env m (Mod_declarations.mod_type t1) (Mod_declarations.mod_type t2)

(************************************************************************)
(** {6 The run} *)

type t = {
  cfg : config;
  dir : string;
  out : string;
  files : string list;           (** the challenge files, absolute or as given *)
  prechecked : DirPath.t list;
  add_challenge_load_path : unit -> unit;
  under_challenge_root : DirPath.t -> bool;
      (** Is this library name under a root the challenge directory stands in
          for? Those are the answer's own libraries. Every other library the
          answer loaded is a shared one: it comes from the image, by the same
          name and the same file on both sides. *)
  open_roots : (DirPath.t * string) list;
      (** The roots the command line binds that the challenge does NOT stand
          in for, with the directory each is bound to. A library under one of
          them is the answer's side of the run and the challenge has no
          counterpart for it, so [check_open_roots] refuses the run unless
          the config pins it. *)
}

let dirpath_of_string s =
  match String.split_on_char '.' s with
  | [] -> cfg_error ("the library name " ^ s ^ " is empty")
  | l -> DirPath.make (List.rev_map Id.of_string l)

(* Before anything is loaded: the files the config pins must be there and have
   the sha256 it gives. *)
let prepare cfg ~dir ~out ~add_challenge_load_path ~under_challenge_root ~open_roots =
  let files =
    List.map (fun f ->
        let p = if Filename.is_relative f.cf_path then Filename.concat dir f.cf_path
          else f.cf_path in
        if not (Sys.file_exists p) then
          CErrors.user_err Pp.(str ("The challenge file " ^ p ^ " is not there."));
        let got = Sha256.hex_of_file p in
        if not (String.equal got f.cf_sha256) then
          CErrors.user_err
            (Pp.str ("The challenge file " ^ p ^ " has sha256 " ^ got ^
                     ", and the config pins " ^ f.cf_sha256 ^ "."));
        p)
      cfg.cfg_challenge_files
  in
  (* A run that does not complete must leave no verdict behind: a reader
     that finds yesterday's file would read a verdict for today's answer. *)
  (try Sys.remove out with Sys_error _ -> ());
  { cfg; dir; out; files;
    prechecked = List.map (fun p -> dirpath_of_string p.pc_library) cfg.cfg_prechecked;
    add_challenge_load_path; under_challenge_root; open_roots }

(* The pre-checked libraries are resolved on the answer's load path, which is
   the one in place when this runs. *)
let check_prechecked t =
  List.iter (fun p ->
      let dp = dirpath_of_string p.pc_library in
      let file = CheckLibrary.library_file dp in
      let got = Sha256.hex_of_file file in
      if not (String.equal got p.pc_sha256) then
        CErrors.user_err
          (Pp.str ("The pre-checked library " ^ p.pc_library ^ " is " ^ file ^
                   ", whose sha256 is " ^ got ^ ", and the config pins " ^ p.pc_sha256 ^ ".")))
    t.cfg.cfg_prechecked

(* A root the command line binds that the challenge does not stand in for is
   an open root: the answer's build put files there, and the challenge
   directory holds nothing under it. Such a library is neither compared
   (the challenge has no counterpart) nor pinned, and loading it into the
   challenge environment as a shared one would let a file the answer wrote
   decide a universe constraint on BOTH sides, which is the forgery this
   refuses: the run stops unless the config pre-checks every library the
   answer loaded from under that root, which pins its sha256.

   Production binds one root, the answer's project root, which every checked
   answer library lives under and the challenge therefore stands in for, so
   the list is empty there. A test harness that binds a stand-in for the
   image's libraries pre-checks them, as the config's pre-checked list is
   for. *)
let check_open_roots t ~answer_deps =
  let under root lib =
    let r = DirPath.to_string root and l = DirPath.to_string lib in
    String.equal l r || CString.is_prefix (r ^ ".") l
  in
  List.iter (fun (lib, _) ->
      List.iter (fun (root, path) ->
          if under root lib && not (List.exists (DirPath.equal lib) t.prechecked) then
            CErrors.user_err
              Pp.(str ("The answer loaded the library " ^ DirPath.to_string lib ^
                       " from " ^ path ^ ", bound to " ^ DirPath.to_string root ^
                       ", which the challenge does not stand in for and the config \
                        does not declare pre-checked. Every library of such a root \
                        must be pre-checked, so that its bytes are pinned.")))
        t.open_roots)
    answer_deps

let rec mp_root mp = match mp with
  | ModPath.MPfile dp -> Some dp
  | ModPath.MPdot (mp, _) -> mp_root mp
  | ModPath.MPbound _ -> None

let in_libs libs mp = match mp_root mp with
  | None -> false
  | Some dp -> List.exists (DirPath.equal dp) libs

(* The dependency digests a challenge library and its answer library record
   for a library both sides load must be equal: otherwise the two sides were
   built against different copies of it, and their kernel names would name
   different objects. That is every pre-checked library, and every shared
   library -- one outside the roots the challenge stands in for, which both
   sides read from the image by the same name. Checked before the challenge
   is imported. *)
let check_dep_digests t ~challenge ~answer =
  let digest_of deps dp =
    Array.fold_left (fun acc (d, dg) -> if DirPath.equal d dp then Some dg else acc) None deps
  in
  let same (Safe_typing.Dvo_or_vi x) (Safe_typing.Dvo_or_vi y) = String.equal x y in
  List.iter (fun (lib, ch_deps) ->
      match List.find_opt (fun (l, _) -> DirPath.equal l lib) answer with
      | None -> ()
      | Some (_, an_deps) ->
        Array.iter (fun (dep, ch_digest) ->
            let prechecked = List.exists (DirPath.equal dep) t.prechecked in
            if prechecked || not (t.under_challenge_root dep) then
              match digest_of an_deps dep with
              | Some an_digest when not (same ch_digest an_digest) ->
                CErrors.user_err
                  Pp.(str ("The library " ^ DirPath.to_string lib ^
                           " depends on the " ^
                           (if prechecked then "pre-checked" else "shared") ^
                           " library " ^ DirPath.to_string dep ^
                           " with a different digest on the challenge side and on the \
                            answer side."))
              | _ -> ())
          ch_deps)
    challenge

(* The challenge load, between two swaps of this process's per-library tables.
   The challenge libraries have the answer's names, so they need tables of
   their own; nothing of the challenge is left in them afterwards.

   The challenge files' own Require lines decide which shared libraries their
   closure reaches, and the answer's tree may Require more of the image than
   they do. A shared library carries universe constraints, and some of them
   relate levels of OTHER shared libraries, which both sides do know; loading
   one more of the image is not something the answer asserted, so the
   challenge environment loads the same shared libraries the answer did
   (dispatch://BET-901). What is left for the constraint check to catch is a
   constraint the answer's OWN libraries add, which is the answer's doing.

   Only the challenge files' closure is compared declaration by declaration.

   What pins a shared library the answer alone Requires, and so what this
   load rests on: the config's sha256 when it is pre-checked, and otherwise
   only (1) that it is resolved on the same load path, which the challenge
   load changes solely by putting the challenge directory in front of the
   roots it stands in for, so a library outside those roots resolves to the
   same file for both sides; (2) that every library naming it as a
   dependency records the same digest on both sides, which the check above
   has just established; and (3) [check_open_roots], which has already
   refused the run if a root the answer could write to were left open. A
   library that none of the three reaches does not exist: a library comes
   from a bound root or from the image's own load path. Each of the three
   refuses the run rather than reporting a verdict. *)
let load_challenge t senv0 ~answer_deps =
  let saved = CheckLibrary.swap_tables (CheckLibrary.fresh_tables ()) in
  let restore () = ignore (CheckLibrary.swap_tables saved) in
  Fun.protect ~finally:restore (fun () ->
      t.add_challenge_load_path ();
      (* A pre-checked library is NOT a shared one, whatever root it sits
         under. The config names it, and the option puts it on the admit
         list, so the answer's environment holds it whether its tree
         Requires it or not; were it shared too, a config could add a
         library to the CHALLENGE's graph and so decide what the challenge
         stands on. The config pins bytes; it does not say what the
         challenge is. In production this changes nothing -- a pre-checked
         library is a registered answer object, under the root the
         challenge stands in for -- and the challenge still loads one
         whose own files Require it, through its closure. *)
      let shared =
        CList.map_filter (fun (dp, _) ->
            if t.under_challenge_root dp || List.exists (DirPath.equal dp) t.prechecked
            then None else Some dp)
          answer_deps
      in
      let needed, all = CheckLibrary.intern_challenge t.files shared in
      let challenge_deps = CheckLibrary.challenge_deps needed in
      check_dep_digests t ~challenge:(CheckLibrary.challenge_deps all) ~answer:answer_deps;
      let senv = CheckLibrary.import_challenge senv0 all in
      Safe_typing.env_of_safe_env senv, challenge_deps)

(************************************************************************)
(** {6 Comparing the two environments} *)

type failure = { f_name : string; f_reason : string }

(* The identity seed: a level of a library that is one file for both sides.
   That is every shared library -- outside the roots the challenge stands in
   for -- and every pre-checked one. A level no compared declaration names
   is in the map only through this: the body of an opaque proof is never
   compared, so a challenge proof's constraint on such a level would
   otherwise never be asked of the answer. *)
let seed_umap t ~challenge_env ~answer_env =
  let gch = Environ.universes challenge_env and gan = Environ.universes answer_env in
  let an = UGraph.domain gan in
  Univ.Level.Set.fold (fun u m ->
      match Univ.Level.name u with
      | None -> m
      | Some ug ->
        let dp, _, _ = Univ.UGlobal.repr ug in
        let one_file =
          List.exists (DirPath.equal dp) t.prechecked || not (t.under_challenge_root dp)
        in
        if one_file && Univ.Level.Set.mem u an then add_level m u u else m)
    (UGraph.domain gch) empty_umap

(* The two directions are not the same question.

   Every challenge constraint, mapped, must hold in the answer: the answer
   must stand where the challenge stands. It is also where an answer that
   contradicts the challenge is caught: the answer's graph alone is
   consistent, since the kernel checked it, so if the answer entails every
   challenge constraint the union of the two is satisfiable.

   The other direction asks what the answer ADDS, and passes over one shape
   alone: a constraint between two of the IMAGE's levels. A proof adds
   those as a matter of course -- it instantiates the image's definitions,
   and the kernel records what that costs -- and they say nothing about the
   task, since the challenge's statements do not stand on the image's
   levels relative to each other. Today's grade of record, a Checker file
   compiled against the task's statements with the kernel merging the
   proof's constraints into one environment, accepts all of them, and two
   runs of the real task show what refusing them costs: the key failed on
   LinuxProcessSemantics.LinuxProcessSem.Fs.33 <= Stdlib.Logic.Classical_Pred_Type.21
   and the untouched control on Fs.33 < Corelib.Init.Logic.22, each between
   two of the image's levels, every theorem of both runs failing on that
   one line (dispatch://BET-901).

   Every other pair is compared, the challenge's own levels to each other
   AND to the image's. An answer that relates one of the challenge's own
   universes to one of the image's has fixed where that universe sits, and
   a statement over it then says less than the challenge's does: a
   statement that injects Type@{u} into a type at an image level is not
   provable while u and that level are apart, and is provable once the
   answer puts u below it. That is a forgery, and it carries no Constraint
   command -- the Qed records it (the adversarial review of 0de0865d26).

   A config that tolerates [answer-universe-constraints] skips this
   direction alone, and only once the challenge-to-answer direction has
   passed; the declaration comparison, the axiom checks and the kernel
   check are untouched. The flag is recorded on every theorem the answer
   holds only when this direction would have failed. Its object is the
   bounded summary of the skipped constraints, so a passing verdict says
   what it cost.

   Both directions compare the PROJECTION of one graph onto the mapped
   levels ([constraints_for], which walks on through a level it does not
   keep), so a path through levels the map does not hold is compared like a
   direct edge, and a forgery cannot be routed around.

   Every failing constraint is reported, not the first: a run that names one
   costs another run to learn whether there are more. *)
let check_constraints t ~challenge_env ~answer_env m =
  let gch = Environ.universes challenge_env and gan = Environ.universes answer_env in
  let own u = match Univ.Level.name u with
    | None -> false
    | Some ug -> let dp, _, _ = Univ.UGlobal.repr ug in t.under_challenge_root dp
  in
  let kept_ch = Univ.Level.Map.domain m.fwd and kept_an = Univ.Level.Map.domain m.bwd in
  (* [constraints_for ~kept] emits only constraints between kept levels, and
     the kept set IS the map's domain, so a level with no image cannot reach
     here. It is an anomaly rather than a pass: a constraint passed over in
     silence is a check that did not run. *)
  let image map u = match Univ.Level.Map.find_opt u map with
    | Some v -> v
    | None ->
      CErrors.anomaly
        Pp.(str ("The comparator projected a universe constraint onto " ^
                 Univ.Level.to_string u ^ ", which its level map does not hold."))
  in
  let shown = 5 in
  let fails ~skip map graph cs =
    let bad = Univ.UnivConstraints.fold (fun (u, k, v) acc ->
        let u' = image map u and v' = image map v in
        if skip u' v' || UGraph.check_constraint graph (u', k, v') then acc
        else
          Printf.sprintf "%s %s %s"
            (Univ.Level.to_string u)
            (match k with Univ.UnivConstraint.Lt -> "<" | Le -> "<=" | Eq -> "=")
            (Univ.Level.to_string v) :: acc)
        cs []
    in
    match List.sort String.compare bad with
    | [] -> None
    | l ->
      let n = List.length l in
      let head = CList.firstn (min shown n) l in
      Some (Printf.sprintf "the constraint %s does not hold on the other side%s"
              (String.concat ", " head)
              (if n > shown then Printf.sprintf " (and %d more)" (n - shown) else ""))
  in
  let never _ _ = false in
  match fails ~skip:never m.fwd gan (UGraph.constraints_for ~kept:kept_ch gch) with
  | Some e -> Some ("the challenge has a universe constraint the answer does not: " ^ e), None
  | None ->
    let both_image u' v' = not (own u') && not (own v') in
    match fails ~skip:both_image m.bwd gch (UGraph.constraints_for ~kept:kept_an gan) with
    | Some e when List.mem_assoc answer_universe_constraints t.cfg.cfg_flags -> None, Some e
    | Some e -> Some ("the answer has a universe constraint the challenge does not: " ^ e), None
    | None -> None, None

(* Every challenge declaration, in the order the name sorts. A declaration the
   answer does not hold is a failure; a declaration only the answer holds is
   not visited. *)
let compare_declarations t ~challenge_env ~answer_env ~libs ~theorems =
  let m = ref (seed_umap t ~challenge_env ~answer_env) in
  let failures = ref [] in
  let fail name reason = failures := { f_name = name; f_reason = reason } :: !failures in
  let deferred = ref [] in
  let step name f =
    match f !m with
    | m' -> m := m'
    | exception Diff d -> fail name d
    | exception Undecided _ -> deferred := (name, f) :: !deferred
  in
  Environ.fold_constants (fun c cb () ->
      if in_libs libs (Constant.modpath c) then
        let name = Constant.to_string c in
        match Environ.lookup_constant_opt c answer_env with
        | None -> fail name "missing"
        | Some cb' ->
          step name (fun m ->
              eq_const_body ~env:answer_env ~is_theorem:(CString.Set.mem name theorems)
                m cb cb'))
    challenge_env ();
  Environ.fold_inductives (fun i mib () ->
      if in_libs libs (MutInd.modpath i) then
        let name = MutInd.to_string i in
        if not (Environ.mem_mind i answer_env) then fail name "missing"
        else step name (fun m -> eq_mib_body m mib (Environ.lookup_mind i answer_env)))
    challenge_env ();
  let an_modtypes = (Environ.Internal.View.view answer_env).Environ.Internal.View.env_modtypes in
  ModPath.Map.iter (fun mp mt ->
      if in_libs libs mp then
        let name = ModPath.to_string mp in
        match ModPath.Map.find_opt mp an_modtypes with
        | None -> fail name "missing"
        | Some mt' -> step name (fun m -> eq_modtype ~env:answer_env m mt mt'))
    (Environ.Internal.View.view challenge_env).Environ.Internal.View.env_modtypes;
  (* The declarations set aside as undecided, again, until a pass decides
     none of them; what is still undecided then fails with its reason. *)
  let rec again pending =
    let progress = ref false in
    let still = List.filter (fun (name, f) ->
        match f !m with
        | m' -> m := m'; progress := true; false
        | exception Diff d -> fail name d; progress := true; false
        | exception Undecided _ -> true)
        pending
    in
    if not (CList.is_empty still) then
      if !progress then again still
      else List.iter (fun (name, f) ->
          match f !m with
          | _ -> ()
          | exception (Diff d | Undecided d) -> fail name d) still
  in
  again (List.rev !deferred);
  let universes, skipped_answer_constraints =
    check_constraints t ~challenge_env ~answer_env !m
  in
  List.rev !failures, universes, skipped_answer_constraints

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

(* Every constant of [env] under its kernel name. *)
let kernel_index env =
  Environ.fold_constants (fun c _ acc -> KNmap.add (Constant.user c) c acc) env KNmap.empty

(* Where an object lives, in words, for a refusal: "the constant g of
   module Q of the library R.P". *)
let describe_object obj =
  let rec path = function
    | ModPath.MPfile dp -> "the library " ^ DirPath.to_string dp
    | ModPath.MPdot (mp, l) -> "module " ^ Label.to_string l ^ " of " ^ path mp
    | ModPath.MPbound _ as mp -> "the functor parameter " ^ ModPath.to_string mp
  in
  match obj with
  | GlobRef.ConstRef c ->
    "the constant " ^ Label.to_string (Constant.label c) ^ " of " ^ path (Constant.modpath c)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    "the inductive block " ^ Label.to_string (MutInd.label mind) ^ " of " ^ path (MutInd.modpath mind)
  | GlobRef.VarRef id -> "the section variable " ^ Id.to_string id


(* Only a rewrite rule the answer itself declares is the answer's doing: a
   pre-checked library may carry its own, and the task did not write it. *)
let has_rewrite_rules env libs =
  Cmap_env.exists (fun c _ -> in_libs libs (Constant.modpath c))
    (Environ.Internal.View.view env).Environ.Internal.View.env_symb_pats

(* A permitted axiom is a declaration the task hands the agent, so it is
   matched by its kernel name, not by the name it prints: a module path and
   a library path can print alike, and the constant [g] of a module [Q] of
   the library [R.P] prints [R.P.Q.g], the name of the constant [g] of the
   library [R.P.Q]. An axiom constant the answer's proof reaches is the
   task's declaration when either
   - its module path, followed through every [MPdot] to its [MPfile], is
     rooted at a pre-checked library. The config pins that library's bytes
     by digest, so no answer file can add a constant under its [MPfile].
     The constant may be a field of a sealed module that the library does
     not export: the closure walk reaches it through the implementation,
     where no environment lookup sees it, and it is still the library's
     own; or
   - both the challenge environment and the answer environment declare the
     same kernel name (the challenge's own files, which the declaration
     comparison holds the answer to, and the libraries both sides read from
     one file). These lookups see only exported fields. Requiring the
     answer's to export it keeps the constant under that comparison: an
     answer that seals a challenge module, hides its axiom and gives it
     another type is refused. An axiom hidden inside a sealed module of a
     challenge file is refused even when the challenge hides it too:
     fail-closed, since the comparison does not see such a field.
   A forged constant declared in a changed file has a module path rooted
   at that file, so its kernel name is neither under a pre-checked
   [MPfile] nor one the challenge declares.
   The same rule, on the inductive block's kernel name, decides whether a
   tolerated flag's object is the task's own. An axiom that is no constant
   is reached only when no library declares it, so the verdict counts it
   as no declaration of the task's without asking this rule. *)
let task_declares t ~challenge_env ~answer_env = function
  | GlobRef.ConstRef c ->
    in_libs t.prechecked (Constant.modpath c)
    || (Environ.mem_constant c challenge_env && Environ.mem_constant c answer_env)
  | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
    in_libs t.prechecked (MutInd.modpath mind)
    || (Environ.mem_mind mind challenge_env && Environ.mem_mind mind answer_env)
  | GlobRef.VarRef _ -> false

(* Why [task_declares] refused [obj], for the refusal's text. *)
let why_not_task ~challenge_env ~answer_env obj =
  let ch, an = match obj with
    | GlobRef.ConstRef c -> Environ.mem_constant c challenge_env, Environ.mem_constant c answer_env
    | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) ->
      Environ.mem_mind mind challenge_env, Environ.mem_mind mind answer_env
    | GlobRef.VarRef _ -> false, false
  in
  let why =
    match obj with
    | GlobRef.VarRef _ -> "a section variable is no declaration of the task's"
    | _ ->
      if ch && not an then
        "the challenge declares it but the answer does not export it, and no pre-checked \
         library holds it"
      else
        "the challenge does not declare it (or hides it in a sealed module), and no \
         pre-checked library holds it"
  in
  "the proof reaches " ^ describe_object obj ^ ": " ^ why

let run t env access senv0 ~answer_deps =
  check_open_roots t ~answer_deps;
  check_prechecked t;
  let challenge_env, all_deps = load_challenge t senv0 ~answer_deps in
  (* A pre-checked library, and every library it rests on, is one file for
     both sides: its declarations are equal by construction, and walking
     them would read the whole standard library on every run. *)
  let rec closure acc = function
    | [] -> acc
    | dp :: tl ->
      if List.exists (DirPath.equal dp) acc then closure acc tl
      else
        let deps = match List.find_opt (fun (l, _) -> DirPath.equal l dp) all_deps with
          | None -> []
          | Some (_, a) -> Array.to_list (Array.map fst a)
        in
        closure (dp :: acc) (deps @ tl)
  in
  let skip = closure [] t.prechecked in
  let libs =
    CList.map_filter (fun (dp, _) ->
        if List.exists (DirPath.equal dp) skip then None else Some dp)
      all_deps
  in
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
  List.iter (fun th -> ignore (ch_theorem th)) t.cfg.cfg_theorems;
  let theorems =
    List.fold_left (fun acc th -> CString.Set.add th.th_name acc) CString.Set.empty
      t.cfg.cfg_theorems
  in
  let failures, universes, skipped_answer_constraints =
    compare_declarations t ~challenge_env ~answer_env:env ~libs ~theorems
  in
  let failed_decl =
    List.fold_left (fun acc f -> CString.Map.add f.f_name f.f_reason acc) CString.Map.empty failures
  in
  (* The theorem a verdict reads is the answer's constant of the challenge
     theorem's kernel name, not whichever answer constant prints its name:
     a module Q of the library R.P holding a constant thm prints R.P.Q.thm,
     the name of the theorem thm of the library R.P.Q. *)
  let an_index = constant_index env in
  let an_kernel = kernel_index env in
  let rewrite_rules = has_rewrite_rules env libs && not t.cfg.cfg_rewrite_rules in
  let st = Check_closure.closure_state env access in
  let records =
    List.map (fun th ->
        let permitted = match th.th_axioms with
          | Some l -> l
          | None -> t.cfg.cfg_axioms
        in
        let verdict, reason, axioms, flags =
          let printing = Option.default [] (CString.Map.find_opt th.th_name an_index) in
          match KNmap.find_opt (Constant.user (ch_theorem th)) an_kernel with
          | None -> "fail", "missing", [], []
          | Some kn ->
            let axioms, flags = Check_closure.axioms_and_flags st kn in
            let flags = List.map (fun (k, o, obj) -> k, o, Some obj) flags in
            let flags =
              match skipped_answer_constraints with
              | Some constraints ->
                (answer_universe_constraints, constraints, None) :: flags
              | None -> flags
            in
            let bad_axioms = List.filter (fun (a, _) -> not (List.mem a permitted)) axioms in
            (* A permitted name the proof reaches through an object the
               task did not declare: a forgery of that name. *)
            let forged_axioms =
              List.filter (fun (a, obj) ->
                  List.mem a permitted
                  && not (match obj with
                      | GlobRef.ConstRef _ -> task_declares t ~challenge_env ~answer_env:env obj
                      | GlobRef.IndRef _ | GlobRef.ConstructRef _ | GlobRef.VarRef _ -> false))
                axioms
            in
            let axioms = CString.Set.elements (CString.Set.of_list (List.map fst axioms)) in
            (* A config entry tolerates a flag when it names the same kind
               and either no object at all, or the flag's object by the name
               it prints AND that object is the task's own declaration of
               that name, by the rule for permitted axioms
               ([task_declares]). *)
            let names_it (kind, printed, _) (k, o) =
              String.equal k kind && (match o with None -> true | Some o -> String.equal o printed)
            in
            let tolerated ((_, _, obj) as f) =
              List.exists (fun ((_, o) as entry) ->
                  names_it f entry
                  && (match o, obj with
                      | None, _ -> true
                      | Some _, Some obj -> task_declares t ~challenge_env ~answer_env:env obj
                      | Some _, None -> false))
                t.cfg.cfg_flags
            in
            let bad_flags = List.filter (fun f -> not (tolerated f)) flags in
            (* The verdict prints each (kind, printed object) once, in the
               order of [flags]: sorted, after any skipped constraints. *)
            let flags =
              List.fold_right (fun (k, o, _) acc ->
                  match acc with
                  | (k', o') :: _ when String.equal k k' && String.equal o o' -> acc
                  | _ -> (k, o) :: acc)
                flags []
            in
            (* A challenge declaration the answer changed is a changed task,
               whichever theorem names it: the statements are written against
               those definitions, so no theorem of the run can pass. The
               theorem's own record names its own difference when it has one. *)
            let reason =
              if List.length printing > 1 then
                Some ("the answer declares " ^ string_of_int (List.length printing) ^
                      " constants that print the theorem's name")
              else
              match CString.Map.find_opt th.th_name failed_decl with
              | Some d -> Some d
              | None ->
                match failures with
                | f :: _ ->
                  Some ("the challenge declaration " ^ f.f_name ^ " differs: " ^ f.f_reason)
                | [] ->
                  match universes with
                  | Some u -> Some u
                  | None ->
                    if rewrite_rules then Some "the answer declares a rewrite rule"
                    else match bad_axioms with
                      | (a, _) :: _ -> Some ("the axiom " ^ a ^ " is not permitted")
                      | [] ->
                      match forged_axioms with
                      | (a, obj) :: _ ->
                        Some ("the axiom " ^ a ^ " is not the task's declaration of that name: " ^
                              why_not_task ~challenge_env ~answer_env:env obj)
                      | [] ->
                        match bad_flags with
                        | ((k, o, obj) as f) :: _ ->
                          let by_name =
                            List.exists (fun ((_, e) as entry) -> Option.has_some e && names_it f entry)
                              t.cfg.cfg_flags
                          in
                          Some ("the relaxed typing flag " ^ k ^ " on " ^ o ^ " is not tolerated" ^
                                match by_name, obj with
                                | true, Some obj ->
                                  ": the config tolerates it on that name, but " ^ o ^
                                  " is not the task's declaration of that name: " ^
                                  why_not_task ~challenge_env ~answer_env:env obj
                                | _ -> "")
                        | [] -> None
            in
            (match reason with
             | Some r -> "fail", r, axioms, flags
             | None -> "pass", "", axioms, flags)
        in
        Json.Obj [
          "name", Json.Str th.th_name;
          "verdict", Json.Str verdict;
          "reason", Json.Str reason;
          "axioms", Json.List (List.map (fun a -> Json.Str a) axioms);
          "flags", Json.List (List.map (fun (k, o) -> Json.Obj ["kind", Json.Str k;
                                                                "object", Json.Str o]) flags);
        ])
      t.cfg.cfg_theorems
  in
  let decls =
    List.map (fun f -> Json.Obj ["name", Json.Str f.f_name; "reason", Json.Str f.f_reason])
      failures
    @ (match universes with
       | None -> []
       | Some u -> [Json.Obj ["name", Json.Str "<universes>"; "reason", Json.Str u]])
  in
  let doc = Json.Obj [
      "format", Json.Int 1;
      "theorems", Json.List records;
      "declarations", Json.List decls;
    ] in
  let ch = open_out t.out in
  Fun.protect ~finally:(fun () -> close_out ch) (fun () ->
      output_string ch (Json.to_string doc);
      output_char ch '\n')
