(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* A small, dependency-free SHA-256 (FIPS 180-4) used only to derive content
   addresses for the checker's native-conversion compile cache (see
   [Nativecache]). Not a general-purpose crypto library: it exists so that
   cache keys do not depend on an external [sha256sum] process per cast. *)

let k = [|
  0x428a2f98l; 0x71374491l; 0xb5c0fbcfl; 0xe9b5dba5l;
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
  0x90befffal; 0xa4506cebl; 0xbef9a3f7l; 0xc67178f2l;
|]

let h0 = [|
  0x6a09e667l; 0xbb67ae85l; 0x3c6ef372l; 0xa54ff53al;
  0x510e527fl; 0x9b05688cl; 0x1f83d9abl; 0x5be0cd19l;
|]

let ( +% ) = Int32.add
let ( &% ) = Int32.logand
let ( |% ) = Int32.logor
let ( ^% ) = Int32.logxor
let lnot32 = Int32.lognot

let rotr x n = Int32.logor (Int32.shift_right_logical x n) (Int32.shift_left x (32 - n))
let shr x n = Int32.shift_right_logical x n

(* Pad [msg] to a whole number of 64-byte blocks per FIPS 180-4 section 5.1.1. *)
let pad msg =
  let len = String.length msg in
  let bit_len = Int64.of_int (len * 8) in
  let pad_len =
    let rem = (len + 1) mod 64 in
    if rem <= 56 then 56 - rem else 120 - rem
  in
  let buf = Buffer.create (len + 1 + pad_len + 8) in
  Buffer.add_string buf msg;
  Buffer.add_char buf '\x80';
  Buffer.add_string buf (String.make pad_len '\x00');
  for i = 7 downto 0 do
    Buffer.add_char buf (Char.chr (Int64.to_int (Int64.logand (Int64.shift_right_logical bit_len (i * 8)) 0xFFL)))
  done;
  Buffer.contents buf

let digest_bytes (msg : string) : string =
  let padded = pad msg in
  let nblocks = String.length padded / 64 in
  let h = Array.copy h0 in
  let w = Array.make 64 0l in
  let byte s i = Int32.of_int (Char.code s.[i]) in
  for b = 0 to nblocks - 1 do
    let base = b * 64 in
    for t = 0 to 15 do
      let i = base + (t * 4) in
      w.(t) <-
        Int32.logor
          (Int32.shift_left (byte padded i) 24)
          (Int32.logor
             (Int32.shift_left (byte padded (i + 1)) 16)
             (Int32.logor (Int32.shift_left (byte padded (i + 2)) 8) (byte padded (i + 3))))
    done;
    for t = 16 to 63 do
      let s0 = (rotr w.(t - 15) 7) ^% (rotr w.(t - 15) 18) ^% (shr w.(t - 15) 3) in
      let s1 = (rotr w.(t - 2) 17) ^% (rotr w.(t - 2) 19) ^% (shr w.(t - 2) 10) in
      w.(t) <- w.(t - 16) +% s0 +% w.(t - 7) +% s1
    done;
    let a = ref h.(0) and b' = ref h.(1) and c = ref h.(2) and d = ref h.(3) in
    let e = ref h.(4) and f = ref h.(5) and g = ref h.(6) and hh = ref h.(7) in
    for t = 0 to 63 do
      let s1 = (rotr !e 6) ^% (rotr !e 11) ^% (rotr !e 25) in
      let ch = (!e &% !f) ^% ((lnot32 !e) &% !g) in
      let temp1 = !hh +% s1 +% ch +% k.(t) +% w.(t) in
      let s0 = (rotr !a 2) ^% (rotr !a 13) ^% (rotr !a 22) in
      let maj = (!a &% !b') ^% (!a &% !c) ^% (!b' &% !c) in
      let temp2 = s0 +% maj in
      hh := !g; g := !f; f := !e; e := !d +% temp1;
      d := !c; c := !b'; b' := !a; a := temp1 +% temp2
    done;
    h.(0) <- h.(0) +% !a; h.(1) <- h.(1) +% !b'; h.(2) <- h.(2) +% !c; h.(3) <- h.(3) +% !d;
    h.(4) <- h.(4) +% !e; h.(5) <- h.(5) +% !f; h.(6) <- h.(6) +% !g; h.(7) <- h.(7) +% !hh
  done;
  let out = Bytes.create 32 in
  Array.iteri
    (fun i v ->
      Bytes.set out (i * 4) (Char.chr (Int32.to_int (Int32.logand (Int32.shift_right_logical v 24) 0xFFl)));
      Bytes.set out ((i * 4) + 1) (Char.chr (Int32.to_int (Int32.logand (Int32.shift_right_logical v 16) 0xFFl)));
      Bytes.set out ((i * 4) + 2) (Char.chr (Int32.to_int (Int32.logand (Int32.shift_right_logical v 8) 0xFFl)));
      Bytes.set out ((i * 4) + 3) (Char.chr (Int32.to_int (Int32.logand v 0xFFl))))
    h;
  Bytes.to_string out

let to_hex (digest : string) : string =
  let buf = Buffer.create (String.length digest * 2) in
  String.iter (fun c -> Buffer.add_string buf (Printf.sprintf "%02x" (Char.code c))) digest;
  Buffer.contents buf

(* Hex-encoded SHA-256 of [s]. *)
let hex_digest (s : string) : string = to_hex (digest_bytes s)
