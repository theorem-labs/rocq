(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* SHA-256, as in FIPS 180-4, section 6.2. The words are [int32], so the
   result does not depend on the width of the native integer. *)

let ( +% ) = Int32.add
let ( ^% ) = Int32.logxor
let ( &% ) = Int32.logand

let rotr x n =
  Int32.logor (Int32.shift_right_logical x n) (Int32.shift_left x (32 - n))

let shr = Int32.shift_right_logical

(* The first 32 bits of the fractional parts of the cube roots of the first
   64 primes. *)
let k =
  [| 0x428a2f98l; 0x71374491l; 0xb5c0fbcfl; 0xe9b5dba5l;
     0x3956c25bl; 0x59f111f1l; 0x923f82a4l; 0xab1c5ed5l;
     0xd807aa98l; 0x12835b01l; 0x243185bel; 0x550c7dc3l;
     0x72be5d74l; 0x80deb1fel; 0x9bdc06a7l; 0xc19bf174l;
     0xe49b69c1l; 0xefbe4786l; 0x0fc19dc6l; 0x240ca1ccl;
     0x2de92c6fl; 0x4a7484aal; 0x5cb0a9dcl; 0x76f988dal;
     0x983e5152l; 0xa831c66dl; 0xb00327c8l; 0xbf597fc7l;
     0xc6e00bf3l; 0xd5a79147l; 0x06ca6351l; 0x14292967l;
     0x27b70a85l; 0x2e1b2138l; 0x4d2c6dfcl; 0x53380d13l;
     0x650a7354l; 0x766a0abbl; 0x81c2c92el; 0x92722c85l;
     0xa2bfe8a1l; 0xa81a664bl; 0xc24b8b70l; 0xc76c51a3l;
     0xd192e819l; 0xd6990624l; 0xf40e3585l; 0x106aa070l;
     0x19a4c116l; 0x1e376c08l; 0x2748774cl; 0x34b0bcb5l;
     0x391c0cb3l; 0x4ed8aa4al; 0x5b9cca4fl; 0x682e6ff3l;
     0x748f82eel; 0x78a5636fl; 0x84c87814l; 0x8cc70208l;
     0x90befffal; 0xa4506cebl; 0xbef9a3f7l; 0xc67178f2l |]

(* The first 32 bits of the fractional parts of the square roots of the first
   eight primes. *)
let h0 =
  [| 0x6a09e667l; 0xbb67ae85l; 0x3c6ef372l; 0xa54ff53al;
     0x510e527fl; 0x9b05688cl; 0x1f83d9abl; 0x5be0cd19l |]

type t = {
  h : int32 array;        (* the eight words of the hash so far *)
  w : int32 array;        (* the message schedule of the block in hand *)
  block : Bytes.t;        (* the bytes of a block that is not yet full *)
  mutable block_len : int;
  mutable len : int64;    (* the bytes fed, for the length at the end *)
}

let create () = {
  h = Array.copy h0;
  w = Array.make 64 0l;
  block = Bytes.create 64;
  block_len = 0;
  len = 0L;
}

let compress t b off =
  let w = t.w and h = t.h in
  for i = 0 to 15 do w.(i) <- Bytes.get_int32_be b (off + 4 * i) done;
  for i = 16 to 63 do
    let x = w.(i - 15) in
    let s0 = rotr x 7 ^% rotr x 18 ^% shr x 3 in
    let y = w.(i - 2) in
    let s1 = rotr y 17 ^% rotr y 19 ^% shr y 10 in
    w.(i) <- w.(i - 16) +% s0 +% w.(i - 7) +% s1
  done;
  let a = ref h.(0) and b1 = ref h.(1) and c = ref h.(2) and d = ref h.(3)
  and e = ref h.(4) and f = ref h.(5) and g = ref h.(6) and h1 = ref h.(7) in
  for i = 0 to 63 do
    let s1 = rotr !e 6 ^% rotr !e 11 ^% rotr !e 25 in
    let ch = (!e &% !f) ^% (Int32.lognot !e &% !g) in
    let t1 = !h1 +% s1 +% ch +% k.(i) +% w.(i) in
    let s0 = rotr !a 2 ^% rotr !a 13 ^% rotr !a 22 in
    let maj = (!a &% !b1) ^% (!a &% !c) ^% (!b1 &% !c) in
    let t2 = s0 +% maj in
    h1 := !g; g := !f; f := !e; e := !d +% t1;
    d := !c; c := !b1; b1 := !a; a := t1 +% t2
  done;
  h.(0) <- h.(0) +% !a; h.(1) <- h.(1) +% !b1;
  h.(2) <- h.(2) +% !c;  h.(3) <- h.(3) +% !d;
  h.(4) <- h.(4) +% !e;  h.(5) <- h.(5) +% !f;
  h.(6) <- h.(6) +% !g;  h.(7) <- h.(7) +% !h1

let feed t b pos len =
  t.len <- Int64.add t.len (Int64.of_int len);
  let pos = ref pos and len = ref len in
  if t.block_len > 0 then begin
    let n = min (64 - t.block_len) !len in
    Bytes.blit b !pos t.block t.block_len n;
    t.block_len <- t.block_len + n;
    pos := !pos + n;
    len := !len - n;
    if t.block_len = 64 then begin compress t t.block 0; t.block_len <- 0 end
  end;
  while !len >= 64 do
    compress t b !pos;
    pos := !pos + 64;
    len := !len - 64
  done;
  if !len > 0 then begin
    Bytes.blit b !pos t.block 0 !len;
    t.block_len <- !len
  end

let hex_digits = "0123456789abcdef"

let finish t =
  let bits = Int64.mul t.len 8L in
  (* One 1 bit, then zeroes up to eight bytes short of a block, then the
     length in bits as a big-endian 64-bit number. *)
  let pad = Bytes.make 72 '\000' in
  Bytes.set pad 0 '\x80';
  let zeroes = (56 - (t.block_len + 1) + 64) mod 64 in
  Bytes.set_int64_be pad (1 + zeroes) bits;
  feed t pad 0 (1 + zeroes + 8);
  assert (t.block_len = 0);
  let out = Bytes.create 64 in
  Array.iteri (fun i x ->
      for j = 0 to 7 do
        let nibble = Int32.to_int (shr x ((7 - j) * 4) &% 0xFl) in
        Bytes.set out ((i * 8) + j) hex_digits.[nibble]
      done)
    t.h;
  Bytes.unsafe_to_string out

let string s =
  let t = create () in
  feed t (Bytes.unsafe_of_string s) 0 (String.length s);
  finish t

let file name =
  let ch = open_in_bin name in
  let t = create () in
  let buf = Bytes.create 65536 in
  let rec loop () =
    let n = input ch buf 0 (Bytes.length buf) in
    if n > 0 then begin feed t buf 0 n; loop () end
  in
  let () =
    try loop (); close_in ch
    with e -> close_in_noerr ch; raise e
  in
  finish t
