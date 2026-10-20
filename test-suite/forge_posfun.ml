
type segment = {
  name : string;
  data : string;
}

let magic = 0x436F7121l

let read_u32 bytes offset =
  let value = Int32.to_int (Bytes.get_int32_be bytes !offset) in
  offset := !offset + 4;
  value

let read_u64 bytes offset =
  let value = Bytes.get_int64_be bytes !offset |> Int64.to_int in
  offset := !offset + 8;
  value

let read_file path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let parse path =
  let file = read_file path |> Bytes.of_string in
  let offset = ref 0 in
  let file_magic = Bytes.get_int32_be file !offset in
  offset := !offset + 4;
  if file_magic <> magic then failwith "invalid .vo magic";
  let version = read_u32 file offset in
  let summary_offset = read_u64 file offset in
  offset := summary_offset;
  let count = read_u32 file offset in
  let segments =
    List.init count (fun _ ->
        let name_length = read_u32 file offset in
        let name = Bytes.sub_string file !offset name_length in
        offset := !offset + name_length;
        let position = read_u64 file offset in
        let length = read_u64 file offset in
        let digest = Bytes.sub_string file !offset 16 in
        offset := !offset + 16;
        let data = Bytes.sub_string file position length in
        if Digest.string data <> digest then failwith ("invalid .vo digest for " ^ name);
        { name; data })
  in
  version, segments

let write path version segments =
  let segments = List.sort (fun left right -> String.compare left.name right.name) segments in
  let output = Buffer.create 4096 in
  Buffer.add_int32_be output magic;
  Buffer.add_int32_be output (Int32.of_int version);
  Buffer.add_int64_be output 0L;
  let summary = ref [] in
  List.iter (fun { name; data } ->
      let position = Buffer.length output in
      Buffer.add_string output data;
      let digest = Digest.string data in
      Buffer.add_string output digest;
      summary := (name, position, String.length data, digest) :: !summary)
    segments;
  let summary_offset = Buffer.length output in
  Buffer.add_int32_be output (Int32.of_int (List.length segments));
  List.iter (fun (name, position, length, digest) ->
      Buffer.add_int32_be output (Int32.of_int (String.length name));
      Buffer.add_string output name;
      Buffer.add_int64_be output (Int64.of_int position);
      Buffer.add_int64_be output (Int64.of_int length);
      Buffer.add_string output digest)
    (List.rev !summary);
  let bytes = Buffer.to_bytes output in
  Bytes.set_int64_be bytes 8 (Int64.of_int summary_offset);
  let channel = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr channel)
    (fun () -> output_bytes channel bytes)

let library segments =
  match List.find_opt (fun segment -> String.equal segment.name "library") segments with
  | Some segment -> segment
  | None -> failwith "missing library segment"

let () =
  match Array.to_list Sys.argv with
  | [_; good_path; bad_path; output_path] ->
    let good_version, good_segments = parse good_path in
    let bad_version, bad_segments = parse bad_path in
    if not (Int.equal good_version bad_version) then failwith "incompatible .vo versions";
    let good_library = library good_segments in
    let bad_library = library bad_segments in
    let good_raw = Obj.repr (Marshal.from_string good_library.data 0 : Obj.t) in
    let bad_raw = Obj.repr (Marshal.from_string bad_library.data 0 : Obj.t) in
    if Obj.size good_raw <> 3 || Obj.size bad_raw <> 3 then
      failwith "unexpected library segment layout";
    let good_compiled = Obj.field good_raw 0 in
    let bad_compiled = Obj.field bad_raw 0 in
    if Obj.size good_compiled <> 7 || Obj.size bad_compiled <> 7 then
      failwith "unexpected compiled library layout";
    Obj.set_field bad_compiled 6 (Obj.field good_compiled 6);
    let forged_library = Marshal.to_string (Obj.obj bad_raw : Obj.t) [] in
    let segments =
      List.map (fun segment ->
          if String.equal segment.name "library" then { segment with data = forged_library } else segment)
        good_segments
    in
    write output_path good_version segments
  | _ -> failwith "usage: forge_posfun GOOD.vo BAD.vo OUTPUT.vo"
