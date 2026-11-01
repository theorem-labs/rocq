(* OpacityLog: the line a record is written as, and which file the compiling
   process reads its records back from (library/opacityLog.ml). *)

open OUnit
open Utest

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let q ?library ?table ?(opaque = false) constant =
  { OpacityLog.constant; library; opaque; table }

let show (x : OpacityLog.query) =
  let opt = function None -> "None" | Some s -> Printf.sprintf "Some %S" s in
  Printf.sprintf "{constant=%S; library=%s; opaque=%b; table=%s}"
    x.constant (opt x.library) x.opaque (opt x.table)

let show_opt = function None -> "None" | Some x -> "Some " ^ show x

(* The line without its newline. *)
let line x =
  let l = OpacityLog.encode_line x in
  assert_bool "a line ends with a newline" (l <> "" && l.[String.length l - 1] = '\n');
  String.sub l 0 (String.length l - 1)

let every_byte = String.init 256 Char.chr

let records = [
  q "A.A.c" ~library:"A.A";
  q "A.A.c" ~library:"A.A" ~opaque:true ~table:"A.A";
  q "P.c";
  q "A.A.x\tA.A\t0\t-\nR\tA.A.forged" ~library:"A.A";
  q "-" ~library:"-" ~table:"-" ~opaque:true;
  q "+" ~library:"+2d" ~table:"";
  q "a\rb\000c" ~library:"" ~table:"\n";
  q every_byte ~library:every_byte ~table:every_byte ~opaque:true;
]

let () = add_test "a record line reads back as the same record" (fun () ->
    List.iter (fun x ->
        let l = line x in
        assert_bool ("one line: " ^ show x) (not (String.contains l '\n'));
        assert_equal ~msg:("five fields: " ^ show x) ~printer:string_of_int 5
          (List.length (String.split_on_char '\t' l));
        assert_equal ~msg:"round trip" ~printer:show_opt (Some x) (OpacityLog.decode_line l))
      records)

let () = add_test "distinct records are written as distinct lines" (fun () ->
    let lines = List.map line records in
    assert_equal ~printer:string_of_int (List.length records)
      (List.length (List.sort_uniq String.compare lines));
    let none_or_dash f = line (f None) <> line (f (Some "-")) in
    assert_bool "an absent library is not the library \"-\""
      (none_or_dash (fun library -> q "c" ?library));
    assert_bool "an absent table is not the table \"-\""
      (none_or_dash (fun table -> q "c" ?table));
    assert_bool "an absent table is not the empty table"
      (line (q "c") <> line (q "c" ~table:"")))

let () = add_test "a line that is not a record is refused" (fun () ->
    List.iter (fun l ->
        assert_equal ~msg:(Printf.sprintf "%S" l) ~printer:show_opt None (OpacityLog.decode_line l))
      [ "";
        "garbage";
        (* names written as they are *)
        "R\tA.A.c\tA.A\t1\tA.A";
        "R\tA.A.c\t-\t0\t-";
        (* hexadecimal is lowercase, two digits a byte *)
        "R\t4A\t-\t0\t-";
        "R\t416\t-\t0\t-";
        (* a present library or table has its "+" *)
        "R\t41\t41\t0\t-";
        "R\t41\t-\t0\t41";
        (* the constant is never empty or absent *)
        "R\t\t-\t0\t-";
        "R\t-\t-\t0\t-";
        "R\t41\t-\t2\t-";
        "R\t41\t-\t0\t-\t";
        "X\t41\t-\t0\t-" ];
    assert_equal ~printer:show_opt (Some (q "A")) (OpacityLog.decode_line "R\t41\t-\t0\t-");
    assert_equal ~printer:show_opt (Some (q "A" ~library:"B" ~table:"" ~opaque:true))
      (OpacityLog.decode_line "R\t41\t+42\t1\t+"))

let show_get = function
  | None -> "None"
  | Some l -> "Some [" ^ String.concat "; " (List.map show l) ^ "]"

let append p s =
  let oc = open_out_gen [Open_wronly; Open_append; Open_binary] 0o600 p in
  output_string oc s; close_out oc

let read p = In_channel.with_open_bin p In_channel.input_all
let write p s = Out_channel.with_open_bin p (fun oc -> output_string oc s)

(* One test: the log is made once per process. [set_enabled] sets the log's
   variables in this process's environment, which the test framework checks
   are unchanged by a test: they are set (empty) before the tests run and set
   back after this one. *)
let () =
  Unix.putenv OpacityLog.env_var "";
  Unix.putenv OpacityLog.identity_env_var ""

let () = add_test "the log read back is the file this process made" (fun () ->
    let cwd = Sys.getcwd () in
    let base = Filename.concat cwd "opacitylog_test.tmp" in
    let rm_rf d = ignore (Sys.command (Filename.quote_command "rm" ["-rf"; d])) in
    rm_rf base;
    Sys.mkdir base 0o700;
    Fun.protect ~finally:(fun () ->
        Sys.chdir cwd; rm_rf base;
        Unix.putenv OpacityLog.env_var "";
        Unix.putenv OpacityLog.identity_env_var "") @@ fun () ->
    Sys.chdir base;
    Sys.mkdir "tmp" 0o700; Sys.mkdir "elsewhere" 0o700;
    (* A relative TMPDIR. *)
    Filename.set_temp_dir_name "tmp";
    OpacityLog.set_enabled true;
    let p = OpacityLog.worker_env_value () in
    assert_bool ("the log's path is absolute: " ^ p) (p <> "" && not (Filename.is_relative p));
    let log_dir = Filename.dirname p in
    assert_equal ~msg:"the private directory is in TMPDIR" ~printer:Fun.id
      (Filename.concat base "tmp") (Filename.dirname log_dir);
    assert_equal ~msg:"the private directory mode" ~printer:string_of_int 0o700
      ((Unix.stat log_dir).Unix.st_perm land 0o777);
    assert_equal ~msg:"the log file mode" ~printer:string_of_int 0o600
      ((Unix.stat p).Unix.st_perm land 0o777);
    let get () = OpacityLog.get () in
    assert_equal ~msg:"a new log" ~printer:show_get (Some []) (get ());
    (* A worker's record. *)
    let r = q "A.A.c" ~library:"A.A" ~opaque:true ~table:"A.A" in
    append p (OpacityLog.encode_line r);
    assert_equal ~msg:"a worker's record" ~printer:show_get (Some [r]) (get ());
    (* The directory changes. *)
    Sys.chdir "elsewhere";
    assert_equal ~msg:"after a change of directory" ~printer:show_get (Some [r]) (get ());
    (* Another file at the log's path: with the same bytes, then empty. *)
    let bytes = read p in
    Sys.rename p (p ^ ".moved");
    write p bytes;
    assert_equal ~msg:"a copy of the log's bytes" ~printer:show_get None (get ());
    (* [reset] must truncate the owner descriptor, not the file now at [p]. *)
    OpacityLog.reset ();
    assert_equal ~msg:"the replacement survives reset" ~printer:Fun.id bytes (read p);
    assert_equal ~msg:"the owner log reset through its descriptor" ~printer:Fun.id
      "rocq-opacity-log 2\n" (read (p ^ ".moved"));
    write p "";
    assert_equal ~msg:"an empty file" ~printer:show_get None (get ());
    Sys.remove p;
    assert_equal ~msg:"no file" ~printer:show_get None (get ());
    Sys.rename (p ^ ".moved") p;
    assert_equal ~msg:"the reset log put back" ~printer:show_get (Some []) (get ());
    append p (OpacityLog.encode_line r);
    assert_equal ~msg:"a record after the reset log is put back" ~printer:show_get
      (Some [r]) (get ());
    Unix.truncate p 0;
    assert_equal ~msg:"the log emptied in place" ~printer:show_get None (get ());
    (* A wrong header in the owner file, with the same length as the right one. *)
    write p ("rocq-opacity-log 1\n" ^ OpacityLog.encode_line r);
    assert_equal ~msg:"a wrong header in the owner file" ~printer:show_get None (get ());
    OpacityLog.reset ();
    assert_equal ~msg:"after reset from the wrong header" ~printer:show_get (Some []) (get ());
    append p (OpacityLog.encode_line r);
    assert_equal ~msg:"a record after reset" ~printer:show_get (Some [r]) (get ());
    (* A torn last line. *)
    append p (line r);
    assert_equal ~msg:"a torn last line" ~printer:show_get None (get ()))

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
