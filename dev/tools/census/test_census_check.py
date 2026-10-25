"""Tests for census_check.py.  Run: python3 -m unittest discover -s dev/tools/census"""

import io
import json
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import census_check as cc


def sites_of(src, path="a/x.ml"):
    return cc.scan_source(path, src)


def kinds(sites):
    return [s.kind for s in sites]


class TokenizerTest(unittest.TestCase):
    def test_comments_strings_and_chars_hide_code(self):
        src = (
            '(* try f () with _ -> 0 (* nested *) "str *)" *)\n'
            'let s = "try f () with _ -> 0"\n'
            "let c = '\"' let d = '\\'' let q = {|try x with _ -> 0|}\n"
            "let f (x : 'a) = x\n"
        )
        self.assertEqual(sites_of(src), [])

    def test_tokens_carry_line_numbers(self):
        toks = cc.tokenize("let x =\n  try f () with _ -> 0\n")
        try_tok = [t for t in toks if t.text == "try"][0]
        self.assertEqual(try_tok.line, 2)


class CatchAllTest(unittest.TestCase):
    def test_wildcard_handler(self):
        sites = sites_of("let f () = try g () with _ -> 0\n")
        self.assertEqual(kinds(sites), ["catchall"])
        self.assertEqual(sites[0].line, 1)
        self.assertEqual(sites[0].key, "catchall:a/x.ml:f/_ -> 0")

    def test_wildcard_after_specific_arm(self):
        sites = sites_of("let f () =\n  try g () with\n  | Not_found -> 0\n  | _ -> 1\n")
        self.assertEqual(kinds(sites), ["catchall"])
        self.assertEqual(sites[0].line, 4)

    def test_match_wildcard_is_not_a_handler(self):
        self.assertEqual(sites_of("let f x = match x with | A -> 1 | _ -> 2\n"), [])

    def test_match_inside_try_body_is_not_a_handler(self):
        src = "let f x = try (match x with A -> 1 | _ -> 2) with Not_found -> 0\n"
        self.assertEqual(sites_of(src), [])

    def test_match_inside_handler_arm_takes_later_arms(self):
        src = "let f x = try g x with Not_found -> match x with A -> 1 | _ -> 2\n"
        self.assertEqual(sites_of(src), [])

    def test_noncritical_guard_is_not_a_catch_all(self):
        src = (
            "let f () = try g () with e when CErrors.noncritical e -> 0\n"
            "let h () = try g () with e when noncritical e -> 0\n"
        )
        self.assertEqual(sites_of(src), [])

    def test_other_guard_is_a_catch_all(self):
        src = "let f () = try g () with e when is_ok e -> 0\n"
        self.assertEqual(kinds(sites_of(src)), ["catchall"])

    def test_named_binding_that_drops(self):
        sites = sites_of("let f () = try g () with e -> ()\n")
        self.assertEqual(kinds(sites), ["catchall"])

    def test_named_binding_that_reraises_is_not_listed(self):
        src = (
            "let f () =\n"
            "  try g () with reraise ->\n"
            "    let reraise = Exninfo.capture reraise in\n"
            "    cleanup ();\n"
            "    Exninfo.iraise reraise\n"
            "let h () = try g () with e -> (cleanup (); raise e)\n"
            "let k () = try g () with e -> let info = Exninfo.info e in Exninfo.iraise (e, info)\n"
        )
        self.assertEqual(sites_of(src), [])

    def test_conditional_reraise_is_listed(self):
        src = "let f c = try g () with e -> if c then raise e else 0\n"
        self.assertEqual(kinds(sites_of(src)), ["catchall"])

    def test_raising_another_exception_is_listed(self):
        src = "let f () = try g () with _ -> raise Not_found\nlet h () = try g () with e -> raise (Wrap e)\n"
        self.assertEqual(kinds(sites_of(src)), ["catchall", "catchall"])

    def test_handler_ended_by_in(self):
        src = "let f () =\n  let x = try g () with Not_found -> 0 in\n  match x with _ -> 1\n"
        self.assertEqual(sites_of(src), [])

    def test_match_exception_arm(self):
        src = "let f () = match g () with v -> v | exception _ -> 0\n"
        sites = sites_of(src)
        self.assertEqual(kinds(sites), ["catchall"])
        self.assertEqual(sites[0].key, "catchall:a/x.ml:f/exception _ -> 0")

    def test_duplicate_handlers_get_ordinals(self):
        src = "let f () = (try g () with _ -> 0) + (try h () with _ -> 0)\n"
        keys = [s.key for s in sites_of(src)]
        self.assertEqual(keys, ["catchall:a/x.ml:f/_ -> 0", "catchall:a/x.ml:f/_ -> 0#2"])

    def test_rebinding_to_a_new_exception_is_listed(self):
        src = (
            "let f () = try g () with e -> let e = Wrap e in raise e\n"
            "let h () =\n"
            "  try g () with reraise ->\n"
            "    let reraise, info = Exninfo.capture reraise in\n"
            "    let reraise = UserError (CErrors.iprint (reraise, info)) in\n"
            "    Exninfo.iraise (reraise, info)\n"
        )
        self.assertEqual(kinds(sites_of(src)), ["catchall", "catchall"])

    def test_key_survives_line_shift(self):
        a = sites_of("let f () = try g () with _ -> 0\n")
        b = sites_of("\n\n(* moved *)\nlet f () = try g () with _ -> 0\n")
        self.assertEqual([s.key for s in a], [s.key for s in b])
        self.assertNotEqual(a[0].line, b[0].line)


class RegistrationSiteTest(unittest.TestCase):
    def test_summary_ref_keyed_by_name(self):
        src = 'let tab = Summary.ref ~name:"searchtable" Map.empty\nlet c = Summary.ref_tag 0 ~name:counter_name\n'
        sites = sites_of(src)
        self.assertEqual(kinds(sites), ["summary", "summary"])
        self.assertEqual(sites[0].key, 'summary:a/x.ml:"searchtable"')
        self.assertEqual(sites[1].key, "summary:a/x.ml:c/counter_name")

    def test_summary_name_on_next_line(self):
        src = "let tab =\n  Summary.ref (Map.empty : t)\n    ~name:\"implicits\"\n"
        self.assertEqual([s.key for s in sites_of(src)], ['summary:a/x.ml:"implicits"'])

    def test_declare_summary_and_observable(self):
        src = (
            'let () = Summary.declare_summary "symbols" { freeze; unfreeze; init }\n'
            "module Observer = Summary.MakeObservable (struct let name = \"obs\" end)\n"
            "let () = Summary.declare_ml_modules_summary { f }\n"
        )
        self.assertEqual(
            [s.key for s in sites_of(src)],
            ['summary:a/x.ml:"symbols"', 'summary:a/x.ml:"obs"', "summary:a/x.ml:<top>/declare_ml_modules_summary"],
        )

    def test_declare_object_keyed_by_object_name(self):
        src = (
            "let inScheme : string * t -> obj =\n"
            "  declare_object @@ superglobal_object \"SCHEME\"\n"
            "    ~cache ~subst:None ~discharge\n"
            "let o = Libobject.declare_named_object_full { (default_object \"X\") with cache_function }\n"
        )
        self.assertEqual(
            [s.key for s in sites_of(src)], ['object:a/x.ml:"SCHEME"', 'object:a/x.ml:"X"']
        )

    def test_declare_object_without_maker_keys_whole_argument(self):
        src = "let o = declare_object (option_object (nickname key) stage write)\n"
        self.assertEqual(
            [s.key for s in sites_of(src)], ["object:a/x.ml:o/(option_object (nickname key) stage write)"]
        )

    def test_no_summary_option(self):
        src = "let () = declare_option ~no_summary:true ~kind:BoolKind\n  { optkey = [\"Dump\";\"Bytecode\"] }\n"
        self.assertEqual([s.key for s in sites_of(src)], ['nosummary-option:a/x.ml:"Dump Bytecode"'])

    def test_noncritical_test_in_named_body_is_not_listed(self):
        src = "let f () = try g () with e -> if CErrors.noncritical e then 0 else Exninfo.iraise (Exninfo.capture e)\n"
        self.assertEqual(sites_of(src), [])

    def test_or_pattern_with_wildcard(self):
        src = "let f () = try g () with Not_found | _ -> 0\n"
        self.assertEqual(kinds(sites_of(src)), ["catchall"])

    def test_let_in_and_if_inside_handler_body(self):
        src = (
            "let f () =\n"
            "  try g () with Not_found -> let x = 1 in if x = 1 then 2 else 3\n"
            "  | _ -> 4\n"
        )
        sites = sites_of(src)
        self.assertEqual(kinds(sites), ["catchall"])
        self.assertEqual(sites[0].line, 3)

    def test_libobject_definitions_are_not_uses(self):
        src = "let declare_object odecl =\n  let tag = declare_object_full odecl in tag\n"
        self.assertEqual(sites_of(src, path="library/libobject.ml"), [])

    def test_summary_definitions_are_not_uses(self):
        self.assertEqual(sites_of("let ref ?stage ~name x = x\n", path="library/summary.ml"), [])


def channel_sites_of(src, path="a/x.ml"):
    return cc.scan_channels(path, src)


READ = 'Proof_recorder.read ~row:"%s" ~channel:"%s" ~key:(fun () -> k) ~value:(fun () -> None)'


class ChannelSiteTest(unittest.TestCase):
    def test_read_and_read_by_keyed_by_row_and_channel(self):
        src = (
            "let f k = if Proof_recorder.active () then " + READ % ("7", "hint_db") + "\n"
            'let g k = Proof_recorder.read_by ~row:"7" ~channel:"hint_db" ~id:k ~key:(fun () -> k) ~value:(fun () -> None)\n'
            "let h k = " + READ % ("8", "classes") + "\n"
        )
        sites = channel_sites_of(src)
        self.assertEqual([s.key for s in sites], ["read:a/x.ml:7/hint_db", "read:a/x.ml:8/classes"])
        self.assertEqual([s.line for s in sites], [1, 3])
        self.assertEqual(sites[0].want, ("row", "7"))

    def test_ineligible_keyed_by_reason(self):
        src = 'let timeout n f =\n  Proof_recorder.ineligible ~reason:"timeout" ~detail:(string_of_float n); f ()\n'
        sites = channel_sites_of(src)
        self.assertEqual([s.key for s in sites], ["ineligible:a/x.ml:timeout"])
        self.assertEqual(sites[0].want, ("ineligible", "timeout"))

    def test_register_tables_record_is_a_read(self):
        src = (
            "let () = Proof_recorder.register_tables (fun () ->\n"
            '    [ Proof_record.{ row = "18"; channel = "counter_start"; key = "evar"; value = None } ])\n'
        )
        self.assertEqual([s.key for s in channel_sites_of(src)], ["read:a/x.ml:18/counter_start"])

    def test_record_update_that_sets_a_channel_is_a_read(self):
        src = (
            'let relabel r = { r with channel = "renamed" }\n'
            'let rewhy i = { i with reason = "other" }\n'
            "let bump p = { p with p_depth = p.p_depth + 1 }\n"
        )
        self.assertEqual(
            [s.key for s in channel_sites_of(src)],
            ['read:a/x.ml:relabel/<r>/"renamed"', "ineligible:a/x.ml:other"],
        )

    def test_wrapper_parameter_followed_to_each_call(self):
        src = (
            "let record channel k v =\n"
            "  if Proof_recorder.active () then\n"
            '    Proof_recorder.read_by ~row:"9" ~channel ~id:k ~key:(fun () -> k) ~value:(fun () -> v)\n'
            'let interp_alias k = record "tactic_alias" k None\n'
            'let interp_ltac k = record "tactic_definition" k None\n'
        )
        sites = channel_sites_of(src)
        self.assertEqual([s.key for s in sites], ["read:a/x.ml:9/tactic_alias", "read:a/x.ml:9/tactic_definition"])
        self.assertEqual([s.line for s in sites], [4, 5])

    def test_partial_application_and_qualified_call_followed(self):
        src = (
            "module Recorded = struct\n"
            "  let once tbl key ~channel value =\n"
            '    Proof_recorder.read ~row:"1" ~channel ~key:(fun () -> key) ~value\n'
            "  let constant tbl = once tbl\n"
            "end\n"
            'let lookup kn = Recorded.constant tbl kn ~channel:"constant" (fun () -> None)\n'
        )
        self.assertEqual([s.key for s in channel_sites_of(src)], ["read:a/x.ml:1/constant"])

    def test_value_that_is_not_a_literal_is_named_by_binding(self):
        src = (
            "let read_named r c = Proof_recorder.read ~row:r ~channel:c ~key:(fun () -> \"\") ~value:(fun () -> None)\n"
            "let read = Proof_recorder.read\n"
        )
        sites = channel_sites_of(src)
        self.assertEqual(
            [s.key for s in sites], ["read:a/x.ml:read_named/r/c", "read:a/x.ml:read/<no row>/<no channel>"]
        )
        self.assertEqual([s.want for s in sites], [None, None])

    def test_recorder_open_and_alias_are_listed(self):
        src = (
            "open Proof_recorder\n"
            'let f k = read ~row:"1" ~channel:"x" ~key:(fun () -> k) ~value:(fun () -> None)\n'
            "module R = Proof_recorder\n"
            'let g () = Proof_recorder.(ineligible ~reason:"r" ~detail:"")\n'
        )
        self.assertEqual(kinds(channel_sites_of(src)), ["recorder-open", "recorder-open", "recorder-open"])

    def test_record_format_and_recorder_plumbing_are_not_sites(self):
        fmt = 'let to_read r c = { row = to_str "row" r; channel = to_str "channel" c }\n'
        self.assertEqual(channel_sites_of(fmt, path="lib/proof_record.ml"), [])
        src = (
            "let read ~row ~channel ~key ~value = Queue.add R.{ row; channel; key = key (); value = value () } q\n"
            "let add p ~reason ~detail = Queue.add R.{ reason; detail } p\n"
            "let ineligible ~reason ~detail = add p ~reason ~detail\n"
            'let digest v = ineligible ~reason:"unhashable" ~detail:"x"; "unhashable"\n'
        )
        sites = channel_sites_of(src, path="lib/proof_recorder.ml")
        self.assertEqual([s.key for s in sites], ["ineligible:lib/proof_recorder.ml:unhashable"])

    def test_comments_and_strings_hide_reads(self):
        src = '(* ' + READ % ("1", "x") + ' *)\nlet s = "Proof_recorder.read ~row:\\"1\\" ~channel:\\"x\\""\n'
        self.assertEqual(channel_sites_of(src), [])


class CheckTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = self.tmp.name
        os.makedirs(os.path.join(self.root, "lib"))
        os.makedirs(os.path.join(self.root, "ide"))
        with open(os.path.join(self.root, "lib", "x.ml"), "w") as f:
            f.write('let t = Summary.ref ~name:"tab" 0\nlet f () = try g () with _ -> 0\n')
        with open(os.path.join(self.root, "ide", "y.ml"), "w") as f:
            f.write("let f () = try g () with _ -> 0\n")

    def tearDown(self):
        self.tmp.cleanup()

    def write_rulings(self, sites, scope=None):
        path = os.path.join(self.root, "rulings.json")
        with open(path, "w") as f:
            json.dump({"source": "test", "commit": "0" * 40, "scope": scope or {"include": ["lib"]}, "sites": sites}, f)
        return path

    def run_main(self, *args):
        out = io.StringIO()
        with redirect_stdout(out):
            code = cc.main(list(args))
        return code, out.getvalue()

    def test_all_ruled_passes(self):
        rulings = self.write_rulings(
            {
                'summary:lib/x.ml:"tab"': {"row": "7"},
                "catchall:lib/x.ml:f/_ -> 0": {"ruling": "only reached by a command"},
            }
        )
        code, out = self.run_main("--root", self.root, "--rulings", rulings)
        self.assertEqual(code, 0, out)

    def test_unmapped_site_fails_and_is_listed(self):
        rulings = self.write_rulings({'summary:lib/x.ml:"tab"': {"row": "7"}})
        code, out = self.run_main("--root", self.root, "--rulings", rulings)
        self.assertEqual(code, 1)
        self.assertIn("UNMAPPED catchall:lib/x.ml:f/_ -> 0 lib/x.ml:2", out.splitlines())

    def test_stale_ruling_fails(self):
        rulings = self.write_rulings(
            {
                'summary:lib/x.ml:"tab"': {"row": "7"},
                "catchall:lib/x.ml:f/_ -> 0": {"ineligible": "reached by a tactic"},
                'summary:lib/gone.ml:"old"': {"row": "1"},
            }
        )
        code, out = self.run_main("--root", self.root, "--rulings", rulings)
        self.assertEqual(code, 1)
        self.assertIn('STALE summary:lib/gone.ml:"old"', out.splitlines())

    def test_entry_must_name_exactly_one_known_disposition(self):
        bad = [
            {"row": "99"},
            {},
            {"row": "7", "ruling": "both"},
            {"ruling": ""},
        ]
        for entry in bad:
            rulings = self.write_rulings(
                {'summary:lib/x.ml:"tab"': entry, "catchall:lib/x.ml:f/_ -> 0": {"ruling": "ok"}}
            )
            code, out = self.run_main("--root", self.root, "--rulings", rulings)
            self.assertEqual(code, 1, entry)
            self.assertIn('INVALID summary:lib/x.ml:"tab"', out)

    def test_scope_excludes_unlisted_dirs(self):
        rulings = self.write_rulings(
            {
                'summary:lib/x.ml:"tab"': {"row": "M3"},
                "catchall:lib/x.ml:f/_ -> 0": {"ruling": "ok"},
            }
        )
        code, out = self.run_main("--root", self.root, "--rulings", rulings, "--list")
        self.assertEqual(code, 0, out)
        self.assertNotIn("ide/y.ml", out)
        self.assertIn("lib/x.ml:2\tcatchall:lib/x.ml:f/_ -> 0\truling: ok", out)

    def test_usage_and_read_errors_exit_2(self):
        code, _ = self.run_main("--root", self.root)
        self.assertEqual(code, 2)
        code, _ = self.run_main("--root", self.root, "--rulings", os.path.join(self.root, "missing.json"))
        self.assertEqual(code, 2)
        code, _ = self.run_main("--root", os.path.join(self.root, "nope"), "--rulings", self.write_rulings({}))
        self.assertEqual(code, 2)


class ChannelCheckTest(unittest.TestCase):
    SRC = (
        'let t = Summary.ref ~name:"tab" 0\n'
        "let f k = " + READ % ("7", "hint_db") + "\n"
        "let g k = " + READ % ("8", "classes") + "\n"
        'let h () = Proof_recorder.ineligible ~reason:"timeout" ~detail:"1"\n'
    )
    RULED = {
        "read:lib/x.ml:7/hint_db": {"row": "7"},
        "read:lib/x.ml:8/classes": {"row": "8"},
        "ineligible:lib/x.ml:timeout": {"ineligible": "@timeout"},
    }

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = self.tmp.name
        os.makedirs(os.path.join(self.root, "lib"))
        self.src = os.path.join(self.root, "lib", "x.ml")
        with open(self.src, "w") as f:
            f.write(self.SRC)
        self.rulings = os.path.join(self.root, "rulings.json")
        with open(self.rulings, "w") as f:
            json.dump(
                {"source": "test", "commit": "0" * 40, "scope": {"include": ["lib"]},
                 "sites": {'summary:lib/x.ml:"tab"': {"row": "7"}}},
                f,
            )

    def tearDown(self):
        self.tmp.cleanup()

    def write_channels(self, sites, name="channels.json", source="test"):
        path = os.path.join(self.root, name)
        with open(path, "w") as f:
            json.dump(
                {"source": source, "commit": "0" * 40, "scope": {"include": ["lib"]},
                 "reasons": {"timeout": "every Control.timeout", "other": "another reason"}, "sites": sites},
                f,
            )
        return path

    def run_main(self, *args):
        out = io.StringIO()
        with redirect_stdout(out):
            code = cc.main(["--root", self.root, "--rulings", self.rulings] + list(args))
        return code, out.getvalue()

    def test_ruled_read_sites_pass_with_the_default_channels_file(self):
        self.write_channels(self.RULED)
        code, out = self.run_main()
        self.assertEqual(code, 0, out)

    def test_unmapped_read_site_fails(self):
        sites = dict(self.RULED)
        del sites["read:lib/x.ml:8/classes"]
        self.write_channels(sites)
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertEqual(out.splitlines(), ["UNMAPPED read:lib/x.ml:8/classes lib/x.ml:3"])

    def test_stale_channel_entry_fails(self):
        self.write_channels(dict(self.RULED, **{"read:lib/gone.ml:1/constant": {"row": "1"}}))
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertEqual(out.splitlines(), ["STALE read:lib/gone.ml:1/constant"])

    def test_new_read_site_without_ruling_fails(self):
        self.write_channels(self.RULED)
        self.assertEqual(self.run_main()[0], 0)
        with open(self.src, "a") as f:
            f.write("let k_read k = " + READ % ("15", "keys") + "\n")
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("UNMAPPED read:lib/x.ml:15/keys lib/x.ml:5", out.splitlines())

    def test_disposition_must_repeat_the_code(self):
        bad = [
            ("read:lib/x.ml:7/hint_db", {"row": "8"}),
            ("read:lib/x.ml:7/hint_db", {"ruling": "covered elsewhere"}),
            ("ineligible:lib/x.ml:timeout", {"ineligible": "@other"}),
            ("ineligible:lib/x.ml:timeout", {"ineligible": "timeout"}),
        ]
        for key, entry in bad:
            self.write_channels(dict(self.RULED, **{key: entry}))
            code, out = self.run_main()
            self.assertEqual(code, 1, entry)
            self.assertIn("INVALID " + key + " the code passes", out)

    def test_channels_option_and_source_match(self):
        other = self.write_channels(self.RULED, name="elsewhere.json")
        self.assertEqual(self.run_main("--channels", other)[0], 0)
        # A channels.json beside the rulings file that names another source is not used.
        self.write_channels(self.RULED, source="another tree")
        code, out = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("UNMAPPED read:lib/x.ml:7/hint_db lib/x.ml:2", out.splitlines())

    def test_list_names_channel_sites(self):
        self.write_channels(self.RULED)
        code, out = self.run_main("--list")
        self.assertEqual(code, 0, out)
        self.assertIn("lib/x.ml:2\tread:lib/x.ml:7/hint_db\trow: 7", out.splitlines())
        self.assertIn("lib/x.ml:4\tineligible:lib/x.ml:timeout\tineligible: @timeout", out.splitlines())

    def test_unreadable_channels_file_exits_2(self):
        code, _ = self.run_main("--channels", os.path.join(self.root, "missing.json"))
        self.assertEqual(code, 2)


if __name__ == "__main__":
    unittest.main()
