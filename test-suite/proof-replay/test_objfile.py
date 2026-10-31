#!/usr/bin/env python3
"""The .vo segment-table reader (BET-84, code-quality review MQ-4).

runner.py and vodiff.py each had a reader of the segment table, and only
runner.py's checked its bounds and refused a name written twice.  objfile.py
is now the one reader.  These cases forge each damaged shape:

* input shorter than the 16-byte header        -> must FAIL
* a magic number that is not "Coq!"            -> must FAIL
* a table position past the end or in the header -> must FAIL
* a table cut short, or with bytes after it    -> must FAIL
* a segment outside the header and the table   -> must FAIL
* a name that the table holds twice            -> must FAIL
* a name that is not UTF-8                     -> must FAIL
* a valid table                                -> loads

and read a real .vo from a build, when there is one: every segment's MD5
must be the one the table and the file record (lib/objFile.ml writes both).
That .vo is $PROOF_REPLAY_VO, or Init/Prelude.vo under $ROCQLIB or under the
tree's own `_build/install/default`.  With none of them the case is skipped.

Run: python3 test-suite/proof-replay/test_objfile.py
"""
from __future__ import annotations

import hashlib
import os
import pathlib
import sys
import unittest

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from objfile import MAGIC, segments  # noqa: E402

VERSION = 90200


def forge(payloads, entries=None, magic=MAGIC, table_at=None, tail=b""):
    """The bytes of a .vo with the segments `payloads` (name -> bytes).

    `entries` replaces the table's (name, pos, length, digest) rows,
    `table_at` the table position in the header, and `tail` is added after
    the table."""
    out = bytearray(magic.to_bytes(4, "big") + VERSION.to_bytes(4, "big") + bytes(8))
    rows = []
    for name, payload in payloads.items():
        digest = hashlib.md5(payload).digest()
        rows.append((name.encode(), len(out), len(payload), digest))
        out += payload + digest
    table = len(out)
    rows = rows if entries is None else entries
    out += len(rows).to_bytes(4, "big")
    for name, pos, length, digest in rows:
        out += len(name).to_bytes(4, "big") + name + pos.to_bytes(8, "big") + length.to_bytes(8, "big") + digest
    out[8:16] = (table if table_at is None else table_at).to_bytes(8, "big")
    return bytes(out + tail)


PAYLOADS = {"library": b"library bytes", "opaques": b"opaque proofs", "summary": b""}


def built_vo():
    """A .vo from a build, or None."""
    if os.environ.get("PROOF_REPLAY_VO"):
        return pathlib.Path(os.environ["PROOF_REPLAY_VO"])
    roots = [pathlib.Path(os.environ["ROCQLIB"])] if os.environ.get("ROCQLIB") else []
    roots.append(HERE.parents[1] / "_build" / "install" / "default" / "lib" / "coq")
    for root in roots:
        vo = root / "theories" / "Init" / "Prelude.vo"
        if vo.is_file():
            return vo
    return None


class ForgedTable(unittest.TestCase):
    def rejects(self, needle, data):
        with self.assertRaises(ValueError) as caught:
            segments(data, "forged.vo")
        self.assertIn(needle, str(caught.exception))
        self.assertTrue(str(caught.exception).startswith("forged.vo: "))

    def test_valid_table_loads(self):
        data = forge(PAYLOADS)
        segs = segments(data, "forged.vo")
        self.assertEqual(sorted(segs), sorted(PAYLOADS))
        for name, payload in PAYLOADS.items():
            pos, length, digest = segs[name]
            self.assertEqual(data[pos:pos + length], payload)
            self.assertEqual(digest, hashlib.md5(payload).digest())

    def test_empty_table_loads(self):
        self.assertEqual(segments(forge({}), "forged.vo"), {})

    def test_short_input_fails(self):
        for size in (0, 1, 15):
            with self.subTest(size=size):
                self.rejects("shorter than a header", forge(PAYLOADS)[:size])

    def test_bad_magic_fails(self):
        self.rejects("not a .vo", forge(PAYLOADS, magic=0x8495A6BE))

    def test_table_past_the_end_fails(self):
        data = forge(PAYLOADS)
        self.rejects("the segment table is past the end", forge(PAYLOADS, table_at=len(data) - 3))
        self.rejects("the segment table is past the end", forge(PAYLOADS, table_at=2 ** 40))

    def test_table_inside_the_header_fails(self):
        self.rejects("the segment table starts inside the header", forge(PAYLOADS, table_at=4))

    def test_table_cut_short_fails(self):
        data = forge(PAYLOADS)
        # Inside the last row's name length, and inside its digest.
        for cut in (len(data) - 2 - 32 - len("summary"), len(data) - 1):
            with self.subTest(cut=cut):
                self.rejects("the segment table is cut short", data[:cut])

    def test_count_beyond_the_rows_fails(self):
        data = bytearray(forge(PAYLOADS))
        table = int.from_bytes(data[8:16], "big")
        data[table:table + 4] = (len(PAYLOADS) + 1).to_bytes(4, "big")
        self.rejects("the segment table is cut short", bytes(data))

    def test_name_length_past_the_end_fails(self):
        rows = [(b"library", 16, 0, bytes(16))]
        data = bytearray(forge({"library": b""}, entries=rows))
        table = int.from_bytes(data[8:16], "big")
        data[table + 4:table + 8] = (2 ** 31).to_bytes(4, "big")
        self.rejects("the segment table is cut short", bytes(data))

    def test_bytes_after_the_table_fail(self):
        self.rejects("1 bytes after the segment table", forge(PAYLOADS, tail=b"\0"))

    def test_segment_past_the_table_fails(self):
        rows = [(b"library", 16, len(b"library bytes") + 1, bytes(16))]
        self.rejects("segment library ends past the segment table",
                     forge({"library": b"library bytes"}, entries=rows))

    def test_huge_segment_length_fails(self):
        rows = [(b"library", 16, 2 ** 63, bytes(16))]
        self.rejects("segment library ends past the segment table", forge({"library": b"x"}, entries=rows))

    def test_segment_inside_the_header_fails(self):
        rows = [(b"library", 8, 0, bytes(16))]
        self.rejects("segment library starts inside the header", forge({"library": b""}, entries=rows))

    def test_duplicate_name_fails(self):
        rows = [(b"library", 16, 1, bytes(16)), (b"library", 33, 1, bytes(16))]
        self.rejects("segment library named twice", forge({"a": b"x", "b": b"y"}, entries=rows))

    def test_name_not_utf8_fails(self):
        rows = [(b"\xfflib", 16, 0, bytes(16))]
        self.rejects("a segment name is not UTF-8", forge({"library": b""}, entries=rows))


class BuiltObject(unittest.TestCase):
    def setUp(self):
        self.vo = built_vo()
        if self.vo is None:
            self.skipTest("no built .vo: set PROOF_REPLAY_VO or ROCQLIB, or build the tree")
        self.data = self.vo.read_bytes()

    def test_every_digest_matches(self):
        segs = segments(self.data, self.vo)
        self.assertIn("library", segs)
        self.assertIn("opaques", segs)
        for name, (pos, length, digest) in segs.items():
            with self.subTest(segment=name):
                self.assertEqual(hashlib.md5(self.data[pos:pos + length]).digest(), digest)
                self.assertEqual(self.data[pos + length:pos + length + 16], digest)

    def test_truncated_object_fails(self):
        with self.assertRaises(ValueError):
            segments(self.data[:-1], self.vo)


if __name__ == "__main__":
    unittest.main(verbosity=2)
