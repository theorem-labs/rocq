(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* SHA-256 (FIPS 180-4), for one use: binding a proof record to the digest
   the grading engine took from the registration's manifest (BET-84 P3).
   OCaml 4.14's [Digest] is MD5 only. Words are held in native ints and
   masked to 32 bits, which needs a 63-bit int. *)

let () = assert (Sys.int_size >= 63)

let k = [|
  0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
  0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
  0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
  0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
  0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
  0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
  0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
  0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2;
|]

let mask = 0xffffffff
let rotr x n = ((x lsr n) lor (x lsl (32 - n))) land mask

let digest_hex (s : string) =
  let len = String.length s in
  (* Padding: a 1 bit, zeros, then the bit length as 64 bits, to a multiple
     of 64 bytes. *)
  let padded_len = ((len + 8) / 64 + 1) * 64 in
  let m = Bytes.make padded_len '\000' in
  Bytes.blit_string s 0 m 0 len;
  Bytes.set m len '\x80';
  let bits = len * 8 in
  for i = 0 to 7 do
    Bytes.set m (padded_len - 1 - i) (Char.chr ((bits lsr (8 * i)) land 0xff))
  done;
  let h = [| 0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19 |] in
  let w = Array.make 64 0 in
  for block = 0 to padded_len / 64 - 1 do
    let base = block * 64 in
    for t = 0 to 15 do
      let b i = Char.code (Bytes.get m (base + (4 * t) + i)) in
      w.(t) <- (b 0 lsl 24) lor (b 1 lsl 16) lor (b 2 lsl 8) lor b 3
    done;
    for t = 16 to 63 do
      let s0 = rotr w.(t - 15) 7 lxor rotr w.(t - 15) 18 lxor (w.(t - 15) lsr 3) in
      let s1 = rotr w.(t - 2) 17 lxor rotr w.(t - 2) 19 lxor (w.(t - 2) lsr 10) in
      w.(t) <- (w.(t - 16) + s0 + w.(t - 7) + s1) land mask
    done;
    let a = ref h.(0) and b = ref h.(1) and c = ref h.(2) and d = ref h.(3) in
    let e = ref h.(4) and f = ref h.(5) and g = ref h.(6) and hh = ref h.(7) in
    for t = 0 to 63 do
      let s1 = rotr !e 6 lxor rotr !e 11 lxor rotr !e 25 in
      let ch = (!e land !f) lxor ((lnot !e) land mask land !g) in
      let t1 = (!hh + s1 + ch + k.(t) + w.(t)) land mask in
      let s0 = rotr !a 2 lxor rotr !a 13 lxor rotr !a 22 in
      let maj = (!a land !b) lxor (!a land !c) lxor (!b land !c) in
      let t2 = (s0 + maj) land mask in
      hh := !g; g := !f; f := !e;
      e := (!d + t1) land mask;
      d := !c; c := !b; b := !a;
      a := (t1 + t2) land mask
    done;
    h.(0) <- (h.(0) + !a) land mask; h.(1) <- (h.(1) + !b) land mask;
    h.(2) <- (h.(2) + !c) land mask; h.(3) <- (h.(3) + !d) land mask;
    h.(4) <- (h.(4) + !e) land mask; h.(5) <- (h.(5) + !f) land mask;
    h.(6) <- (h.(6) + !g) land mask; h.(7) <- (h.(7) + !hh) land mask
  done;
  String.concat "" (Array.to_list (Array.map (Printf.sprintf "%08x") h))
