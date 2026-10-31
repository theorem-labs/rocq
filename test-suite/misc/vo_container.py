"""Read and write the segments of a .vo file, for the tests that build one by hand.

The container's layout is lib/objFile.ml's: a magic word, the .vo version, the
position of the summary, the segments, each followed by its digest, and the
summary of their names, positions, lengths and digests. Reading a file and
writing it back unchanged gives the same bytes, so a test that rewrites one
changes only what it means to change.

The tests that rewrite a .vo for the vmlibrary format version use this:
misc/vmlibrary_format_version.sh and misc/rocqchk_vm_bytecode.sh. Other tests
read or write that layout themselves and are left as they are, so a change of
lib/objFile.ml has to look at them too: rocqchk_cook.sh, rocqchk_parallel.sh,
rocqchk_release.sh, rocqchk_lazyopaque.sh (which also needs where each segment
is), library-label-vmlibrary.sh, norec-validation-order/corrupt.ml, and the
summary parsers of rocqchk_binnum_literal.sh and rocqchk_binnum_univ.sh. Moving
them here is a refactor of tests this change does not touch.

Only the test suite uses this; Rocq itself reads and writes the container in
lib/objFile.ml.
"""

import struct

MAGIC = 0x436F7121  # "Coq!"; every integer is big-endian


def read(path):
    """(vo version, {segment name: (bytes, stored digest)}) in the order the
    file holds the segments, with the two stored copies of each segment's
    digest checked against each other.

    The digest a segment stores is not always the MD5 of its bytes: under
    coqc -location-free-label the library segment stores the library's label
    (vernac/library.ml, lib/objFile.mli). The container's own readers
    compare the copy in the summary with the copy after the data and
    recompute neither, so a rewrite carries every segment's digest over, and
    a test that changes a segment's bytes keeps its stored digest. Two
    readers above them hash a segment themselves, so a test that rewrites
    one of those two must expect it: coqc hashes the library segment and
    keeps that library's Print Assumptions entries out of the shared cache
    unless its digest is that MD5 (vernac/library.ml, label_digested), and
    rocq-library-label hashes the keepfacts segment and reads it as absent
    on a mismatch (checker/library_label.ml, read_keep_facts). The two tests
    that use this module rewrite the vmlibrary segment, which neither
    hashes."""
    b = open(path, "rb").read()
    magic, vo_version = struct.unpack_from(">II", b, 0)
    assert magic == MAGIC, "%s: bad magic" % path
    (summary_pos,) = struct.unpack_from(">Q", b, 8)
    off = summary_pos
    (count,) = struct.unpack_from(">I", b, off)
    off += 4
    found = []
    for _ in range(count):
        (name_len,) = struct.unpack_from(">I", b, off)
        off += 4
        name = b[off:off + name_len].decode()
        off += name_len
        pos, length = struct.unpack_from(">QQ", b, off)
        off += 16
        digest = b[off:off + 16]
        off += 16
        data = b[pos:pos + length]
        assert b[pos + length:pos + length + 16] == digest, \
            "%s: %s stores two different digests" % (path, name)
        found.append((pos, name, (data, digest)))
    return vo_version, {name: seg for _, name, seg in sorted(found)}


def write(path, vo_version, segments):
    """Write the segments as a well-formed container: their data in the order
    given, which for what [read] returns is the file's own, each followed by
    the digest it carries, the summary by name, as the CString.Map Rocq keeps
    them in iterates, and every offset recomputed."""
    out = bytearray()
    out += struct.pack(">II", MAGIC, vo_version)
    out += struct.pack(">Q", 0)  # the summary's position, patched below
    summary = []
    for name, (data, digest) in segments.items():
        pos = len(out)
        out += data
        out += digest
        summary.append((name, pos, len(data), digest))
    summary_pos = len(out)
    out += struct.pack(">I", len(summary))
    for name, pos, length, digest in sorted(summary):
        name = name.encode()
        out += struct.pack(">I", len(name)) + name
        out += struct.pack(">QQ", pos, length) + digest
    struct.pack_into(">Q", out, 8, summary_pos)
    open(path, "wb").write(bytes(out))
