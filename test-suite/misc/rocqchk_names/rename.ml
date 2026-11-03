(* Replace every occurrence of a string with another string of the same length
   in the data of one segment of a .vo file. The other segments and every
   checksum are left untouched: rocqchk reads an admitted library without
   validation, so it loads the changed data. A string keeps its length, so the
   marshalled data stays well formed. See lib/objFile.ml for the format.

   Usage: ocaml rename.ml FILE SEGMENT FROM TO *)

let input_int64 ch =
  let rec go i accu =
    if i = 0 then accu
    else go (i - 1) (Int64.logor (Int64.shift_left accu 8) (Int64.of_int (input_byte ch)))
  in
  go 8 0L

let fail msg = prerr_endline msg; exit 1

let () =
  let file = Sys.argv.(1) and segment = Sys.argv.(2) in
  let from = Sys.argv.(3) and into = Sys.argv.(4) in
  let n = String.length from in
  if n = 0 || String.length into <> n then fail "FROM and TO must have the same non-zero length";
  let ch = open_in_bin file in
  let () = seek_in ch 8 in
  let summary_pos = input_int64 ch in
  let () = LargeFile.seek_in ch summary_pos in
  let nsegs = input_binary_int ch in
  let found = ref None in
  for _ = 1 to nsegs do
    let nlen = input_binary_int ch in
    let name = really_input_string ch nlen in
    let pos = input_int64 ch in
    let len = input_int64 ch in
    let _hash = really_input_string ch 16 in
    if String.equal name segment then found := Some (pos, len)
  done;
  let pos, len = match !found with
    | Some seg -> seg
    | None -> fail ("no segment " ^ segment ^ " in " ^ file)
  in
  let () = LargeFile.seek_in ch pos in
  let data = Bytes.of_string (really_input_string ch (Int64.to_int len)) in
  close_in ch;
  let matches_at i =
    let rec go j = j = n || (Bytes.get data (i + j) = from.[j] && go (j + 1)) in
    go 0
  in
  let count = ref 0 in
  let i = ref 0 in
  while !i + n <= Bytes.length data do
    if matches_at !i then begin
      Bytes.blit_string into 0 data !i n;
      incr count;
      i := !i + n
    end
    else incr i
  done;
  if !count = 0 then fail (Printf.sprintf "no %S in segment %s of %s" from segment file);
  let ch = open_out_gen [Open_wronly; Open_binary] 0o644 file in
  let () = LargeFile.seek_out ch pos in
  output_bytes ch data;
  close_out ch;
  Printf.printf "%s: replaced %d occurrence(s) of %S with %S in segment %s\n"
    file !count from into segment
