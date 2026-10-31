"""The segment table of a .vo file, read strictly (BET-84).

`lib/objFile.ml` writes a .vo as:

    int32   magic number 0x436F7121 ("Coq!")
    int32   Rocq version
    int64   absolute position of the segment table
    ...     segments, each one its bytes and then their MD5 (16 bytes)
    table   int32 count, then per segment: int32 name length, the name,
            int64 position, int64 length (without the MD5), the MD5

`close_out` writes the table last, so the table ends at the end of the file,
and every segment lies between the header and the table.  `segments` checks
all of this, and refuses a name that the table holds twice, so that a
damaged or misread object stops the caller and is never compared by halves.
It does not check the version: the replay tools compare objects of any
Rocq version.  The OCaml reader is `ObjFile.open_in` and
`ObjFile.segment_of_string`.
"""

from collections import namedtuple

MAGIC = 0x436F7121
HEADER = 16  # magic, version, table position
DIGEST = 16  # the MD5 after each segment, and in its table entry

#: One segment: its absolute position, its length without the MD5, and the
#: MD5 that the table records.
Segment = namedtuple("Segment", "pos length digest")


def segments(data, what):
    """The segment table of the .vo bytes `data`: name -> Segment.

    `what` names the object in an error.  Raises ValueError when the bytes
    are not a .vo that `lib/objFile.ml` can have written.
    """
    size = len(data)
    if size < HEADER:
        raise ValueError("%s: shorter than a header" % what)
    magic = int.from_bytes(data[0:4], "big")
    if magic != MAGIC:
        raise ValueError("%s: magic number %08x, not a .vo" % (what, magic))
    table = int.from_bytes(data[8:16], "big")
    if table < HEADER:
        raise ValueError("%s: the segment table starts inside the header" % what)
    if table + 4 > size:
        raise ValueError("%s: the segment table is past the end" % what)
    count = int.from_bytes(data[table:table + 4], "big")
    off, segs = table + 4, {}
    for _ in range(count):
        if off + 4 > size:
            raise ValueError("%s: the segment table is cut short" % what)
        nlen = int.from_bytes(data[off:off + 4], "big")
        off += 4
        if off + nlen + 16 + DIGEST > size:
            raise ValueError("%s: the segment table is cut short" % what)
        try:
            name = data[off:off + nlen].decode("utf-8")
        except UnicodeDecodeError:
            raise ValueError("%s: a segment name is not UTF-8: %r" % (what, data[off:off + nlen])) from None
        off += nlen
        pos = int.from_bytes(data[off:off + 8], "big")
        length = int.from_bytes(data[off + 8:off + 16], "big")
        digest = bytes(data[off + 16:off + 16 + DIGEST])
        off += 16 + DIGEST
        if pos < HEADER:
            raise ValueError("%s: segment %s starts inside the header" % (what, name))
        if pos + length + DIGEST > table:
            raise ValueError("%s: segment %s ends past the segment table" % (what, name))
        if name in segs:
            raise ValueError("%s: segment %s named twice" % (what, name))
        segs[name] = Segment(pos, length, digest)
    if off != size:
        raise ValueError("%s: %d bytes after the segment table" % (what, size - off))
    return segs
