(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let version = 1

exception Unsupported of string

(* The C walk raises it by this name. *)
let () = Callback.register_exception "Libkey.Unsupported" (Unsupported "")

external encode : Obj.t -> string = "rocq_libkey_encode"
external sha256 : string -> string = "rocq_libkey_sha256"
external force_portable_sha256 : bool -> unit = "rocq_libkey_force_portable"
external sha256_extensions : unit -> bool = "rocq_libkey_sha_extensions"

let header = lazy begin
  let b = Buffer.create 64 in
  let u32 n = Buffer.add_int32_le b (Int32.of_int n) in
  Buffer.add_string b "rocq-library-label\000";
  u32 version;
  u32 (Int32.to_int Coq_config.vo_version);
  u32 Sys.word_size;
  u32 (String.length Coq_config.caml_version);
  Buffer.add_string b Coq_config.caml_version;
  Buffer.contents b
end

let label v = String.sub (sha256 (Lazy.force header ^ encode v)) 0 16
