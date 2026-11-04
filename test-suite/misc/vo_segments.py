"""Read and write the segments of a .vo file, for tests that build a corrupted one.

The layout is lib/objFile.ml's: a magic number and a version, then the position of the summary; the summary
lists each segment's name, position, length and MD5. All integers are big-endian.

Usage, from a test:  python3 misc/vo_segments.py splice-opaques GOOD.vo BAD.vo OUT.vo
writes OUT.vo with GOOD.vo's segments and BAD.vo's opaques segment, each segment's MD5 recomputed, so the
library declares what GOOD.vo declares and its opaque proofs are BAD.vo's.
"""

import hashlib
import struct
import sys

MAGIC = 0x436F7121  # "Coq!"


def parse(path):
    """The version and the segments of the .vo at ``path``, each checked against its MD5."""
    b = open(path, "rb").read()
    magic, ver = struct.unpack_from(">II", b, 0)
    assert magic == MAGIC, "bad magic"
    (summary,) = struct.unpack_from(">Q", b, 8)
    off = summary
    (n,) = struct.unpack_from(">I", b, off)
    off += 4
    segments = {}
    for _ in range(n):
        (name_len,) = struct.unpack_from(">I", b, off)
        off += 4
        name = b[off : off + name_len].decode()
        off += name_len
        pos, length = struct.unpack_from(">QQ", b, off)
        off += 16
        digest = b[off : off + 16]
        off += 16
        data = b[pos : pos + length]
        assert hashlib.md5(data).digest() == digest, name + ": bad segment MD5"
        segments[name] = data
    return ver, segments


def write(path, ver, segments):
    """A .vo at ``path`` holding ``segments``, with their MD5s and the summary recomputed."""
    out = bytearray(struct.pack(">II", MAGIC, ver))
    out += struct.pack(">Q", 0)
    summary = []
    for name in sorted(segments):
        data = segments[name]
        pos = len(out)
        out += data
        digest = hashlib.md5(data).digest()
        out += digest
        summary.append((name, pos, len(data), digest))
    summary_pos = len(out)
    out += struct.pack(">I", len(summary))
    for name, pos, length, digest in summary:
        encoded = name.encode()
        out += struct.pack(">I", len(encoded)) + encoded + struct.pack(">QQ", pos, length) + digest
    struct.pack_into(">Q", out, 8, summary_pos)
    open(path, "wb").write(out)


def splice_opaques(good, bad, out):
    ver_good, good_segments = parse(good)
    ver_bad, bad_segments = parse(bad)
    assert ver_good == ver_bad, "the two files were compiled by different versions"
    assert good_segments["opaques"] != bad_segments["opaques"], "the opaques segments are the same"
    spliced = dict(good_segments)
    spliced["opaques"] = bad_segments["opaques"]
    write(out, ver_good, spliced)


if __name__ == "__main__":
    if len(sys.argv) == 5 and sys.argv[1] == "splice-opaques":
        splice_opaques(*sys.argv[2:])
    else:
        sys.exit(__doc__)
