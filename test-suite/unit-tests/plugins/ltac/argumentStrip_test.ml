open OUnit
open Utest
open Names
open Ltac_plugin

(* Tacentries.argument_extend's optional [?strip] (design D18): an argument
   declared without a stripper (a plugin written before D18) is read by the
   interface key as it is, locations included, so the library that stores
   such a value is not keyless, and a moved location changes its key. *)

let tests = ref []
let add_test name f = tests := mk_test name (TestCase f) :: !tests

let lid = CAst.make ~loc:(Loc.create (Loc.InFile { dirpath = None; file = "/tmp/A.v" }) 3 0 10 11)
    (Id.of_string "x")

let pr _ _ _ _ _ _ = Pp.mt ()

let argument ?strip name : (lident, lident, lident) Genarg.genarg_type =
  fst (Tacentries.argument_extend ~plugin:"libkey-test.plugin" ~name ~ignore_kw:false ?strip
         { Tacentries.arg_parsing = Vernacextend.Arg_alias Procq.Prim.identref;
           arg_tag = None;
           arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
           arg_subst = Tacentries.ArgSubstFun (fun _ v -> v);
           arg_interp = Tacentries.ArgInterpRet;
           arg_printer = (pr, pr, pr) })

let strip wit v =
  Genarg.out_gen (Genarg.glbwit wit) (Genstrip.generic_strip (Genarg.in_gen (Genarg.glbwit wit) v))

let () = add_test "no stripper: the value as it is, locations included" (fun () ->
    let wit = argument "libkey-test-default" in
    match strip wit lid with
    | v ->
      assert_bool "location kept" (Option.has_some v.CAst.loc);
      assert_equal ~printer:Id.to_string (Id.of_string "x") v.CAst.v
    | exception LocStrip.Unknown what -> assert_failure ("no view: " ^ what))

let () = add_test "a stripper given" (fun () ->
    let wit = argument ~strip:(Tacentries.ArgStripFun (LocStrip.cast (fun id -> id))) "libkey-test-stripped" in
    assert_bool "location stripped" (Option.is_empty (strip wit lid).CAst.loc))

let _ = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)
