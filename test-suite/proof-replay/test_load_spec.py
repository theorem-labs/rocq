#!/usr/bin/env python3
"""What `expect.json` may hold (BET-84).

Every key of a fixture's `expect.json` has a default, so the first version of
the loader merged any key into the defaults: a misspelled `tree_dirs`,
`tree_files`, `unpublished` or `replay_file` took its empty default, and the
fixture tested another tree than its author wrote (code-quality review round
2 of 26528c8a34, MQ2-2). These cases forge each shape directly against the
loader, so no fixture has to be broken:

* a misspelled key                           -> must FAIL
* a `tree_dirs` or `tree_files` side that is
  neither `original` nor `edited`            -> must FAIL
* `unpublished` names a file not in `files`  -> must FAIL
* `tree_files` copies a file the fixture
  does not have                              -> must FAIL
* no `files`                                 -> must FAIL
* a valid spec                               -> loads, with the defaults
* every fixture of the suite                 -> loads

Run: python3 test-suite/proof-replay/test_load_spec.py
"""
from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from runner import DEFAULTS, fixture_names, load_spec, spec_of  # noqa: E402


class LoadSpec(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.where = pathlib.Path(tmp.name)
        (self.where / "cache.bin").write_bytes(b"\0")

    def load(self, **keys):
        raw = {"doc": "a forged fixture", "files": ["A.v", "B.v"]}
        raw.update(keys)
        return spec_of("forged", raw, self.where)

    def rejects(self, needle, **keys):
        with self.assertRaises(ValueError) as caught:
            self.load(**keys)
        self.assertIn(needle, str(caught.exception))

    def test_valid_spec_loads_with_defaults(self):
        spec = self.load(unpublished=["B.v"], tree_dirs={"original": [".nia.cache"]},
                         tree_files={"edited": {".lia.cache": "cache.bin"}})
        self.assertEqual(spec["name"], "forged")
        self.assertEqual(spec["unpublished"], ["B.v"])
        self.assertEqual(spec["ratio"], DEFAULTS["ratio"])
        self.assertIsNone(spec["replay_file"])

    def test_misspelled_staging_key_fails(self):
        """The review's case: `tree_dir` would leave `tree_dirs` empty."""
        self.rejects("unknown key 'tree_dir'", tree_dir={"edited": [".nia.cache"]})

    def test_misspelled_publishing_keys_fail(self):
        self.rejects("unknown key 'replayfile', 'unpublised'",
                     unpublised=["B.v"], replayfile="absent.proof-record.jsonl")

    def test_invalid_tree_dirs_side_fails(self):
        self.rejects("`tree_dirs` side 'edit' is not original or edited",
                     tree_dirs={"edit": [".nia.cache"]})

    def test_invalid_tree_files_side_fails(self):
        self.rejects("`tree_files` side 'grade' is not original or edited",
                     tree_files={"grade": {".lia.cache": "cache.bin"}})

    def test_unpublished_outside_files_fails(self):
        self.rejects("`unpublished` names 'C.v'", unpublished=["C.v"])

    def test_tree_files_missing_source_fails(self):
        self.rejects("copies 'absent.bin' to '.lia.cache'",
                     tree_files={"edited": {".lia.cache": "absent.bin"}})

    def test_no_files_fails(self):
        with self.assertRaises(ValueError) as caught:
            spec_of("forged", {"doc": "no files"}, self.where)
        self.assertIn("`files` must be a non-empty list", str(caught.exception))

    def test_every_fixture_loads(self):
        names = fixture_names()
        self.assertTrue(names)
        for name in names:
            with self.subTest(fixture=name):
                load_spec(name)


if __name__ == "__main__":
    unittest.main(verbosity=2)
