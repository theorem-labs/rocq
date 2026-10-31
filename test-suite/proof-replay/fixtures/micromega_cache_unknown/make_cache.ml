(* Writes lia-cache-unknown.bin: a copy of a .lia.cache (the format of
   plugins/micromega/persistent_cache.ml) with the result of every entry
   changed to Certificate.Unknown. The key of each entry, its hash and the
   file's header stay as the plugin wrote them.

   Made from the .lia.cache that a compile of original/A.v writes, with the
   micromega plugin of the same build:
     rocq compile -q -Q . PR A.v
     ocamlfind ocamlopt -thread -package rocq-runtime.plugins.micromega \
       -linkpkg make_cache.ml -o make_cache
     ./make_cache .lia.cache lia-cache-unknown.bin *)

open Micromega_core_plugin

type key = int * (Micromega.z Micromega.pol * Micromega.op1) list

let () =
  let ic = open_in_bin Sys.argv.(1) in
  let oc = open_out_bin Sys.argv.(2) in
  (* The magic number and the cache version, two 32-bit integers. *)
  output_string oc (really_input_string ic 8);
  let rec copy n =
    match input_binary_int ic with
    | exception End_of_file -> n
    | hash ->
      let ((k : key), (_ : Micromega_plugin.Certificate.zres)) = Marshal.from_channel ic in
      output_binary_int oc hash;
      Marshal.to_channel oc (k, (Micromega_plugin.Certificate.Unknown : Micromega_plugin.Certificate.zres)) [];
      copy (n + 1)
  in
  let n = copy 0 in
  close_out oc;
  Printf.printf "%d entries, each result now Unknown\n" n
