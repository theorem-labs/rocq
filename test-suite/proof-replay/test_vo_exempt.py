#!/usr/bin/env python3
"""What `vo_exempt` may and may not excuse (BET-84 P3).

GRADE retired byte identity as a correctness gate on 2026-10-26, so a
Marshal sharing difference in the compiled library is a reuse-rate item.
Nothing else is. The first version of the exemption keyed on the fixture's
file name alone, so it would have excused a semantic VALUE difference in
another segment: XP3 showed it at 7cb123ab61 by invoking the reporter with
`what='opaques'` and watching it pass.

These cases forge each shape directly against the decision, so no `.vo`
has to be fabricated:

* a value difference in `library`          -> must FAIL
* a difference in `opaques`                -> must FAIL
* a difference in `library` and `opaques`  -> must FAIL
* an unlisted fixture, sharing only        -> must FAIL
* `library` only, values equal, listed     -> excused

Run: python3 test-suite/proof-replay/test_vo_exempt.py
"""
from __future__ import annotations

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from runner import EXEMPTIBLE_FIXTURES, exemption_allowed  # noqa: E402

LISTED = EXEMPTIBLE_FIXTURES[0]


class Exemption(unittest.TestCase):
    def test_sharing_only_in_library_is_excused(self):
        allowed, why = exemption_allowed(LISTED, ["library"], True)
        self.assertTrue(allowed, why)

    def test_value_difference_in_library_fails(self):
        allowed, why = exemption_allowed(LISTED, ["library"], False)
        self.assertFalse(allowed)
        self.assertIn("VALUES differ", why)

    def test_difference_in_opaques_fails(self):
        """XP3's case: another segment must never be excused."""
        allowed, why = exemption_allowed(LISTED, ["opaques"], True)
        self.assertFalse(allowed)
        self.assertIn("opaques", why)

    def test_library_plus_another_segment_fails(self):
        allowed, why = exemption_allowed(LISTED, ["library", "opaques"], True)
        self.assertFalse(allowed)

    def test_vmlibrary_alone_fails(self):
        allowed, _ = exemption_allowed(LISTED, ["vmlibrary"], True)
        self.assertFalse(allowed)

    def test_unlisted_fixture_is_never_excused(self):
        allowed, why = exemption_allowed("some_other_fixture", ["library"], True)
        self.assertFalse(allowed)
        self.assertIn("not on the exemptible list", why)

    def test_every_listed_fixture_is_named(self):
        """The list is explicit, so adding one is a deliberate act."""
        self.assertEqual(sorted(EXEMPTIBLE_FIXTURES),
                         ["channels_unchanged", "eval_micromega_cache", "hint_removed", "place_same_file",
                          "vm_lia_hit", "write_scheme_rewrite"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
