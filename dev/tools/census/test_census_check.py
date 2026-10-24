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


if __name__ == "__main__":
    unittest.main()
