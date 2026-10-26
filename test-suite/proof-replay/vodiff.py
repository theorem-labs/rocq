#!/usr/bin/env python3
"""Structural diff of two .vo segments (BET-84 P3).

Written for this suite by R1P3.P3Fix3 and vendored here so the runner can
tell a VALUE difference from a Marshal SHARING difference. GRADE retired
byte identity as a correctness gate on 2026-10-26: segments must be
value-equal, and sharing is a reuse-rate item. Only this tool can tell the
two apart, so only it may decide that a fixture's byte difference is
excusable.

The segment holds one OCaml Marshal stream.  This decodes it into a tree,
resolving every shared pointer, so two objects can be compared by VALUE and the
places where only the SHARING differs can be named by their field path.

    vodiff.py REPLAY.vo STOCK.vo [SEGMENT]      (default segment: library)

It prints, in order:
  * value equality of the whole segment,
  * every path where the two values differ,
  * every path where the values are equal but one side wrote a shared pointer
    and the other wrote the value again (the Marshal sharing difference),
    with the shared node printed in short form.
"""
import sys
from pathlib import Path

MAGIC = 0x8495A6BE


class Node:
    __slots__ = ("kind", "tag", "fields", "value", "objno", "shared_at")

    def __init__(self, kind, tag=0, fields=None, value=None, objno=None):
        self.kind = kind          # "int" | "block" | "string" | "double" | "custom" | "other"
        self.tag = tag
        self.fields = fields or []
        self.value = value
        self.objno = objno        # index in the object table, for sharing
        self.shared_at = []       # paths where this node was reached through a shared pointer

    def short(self):
        if self.kind == "int":
            return "int %d" % self.value
        if self.kind == "string":
            return "string %r" % self.value[:40]
        if self.kind == "double":
            return "double %r" % self.value
        if self.kind == "custom":
            return "custom %r" % self.value[:24]
        return "block tag %d, %d field(s): %s" % (
            self.tag, len(self.fields),
            ", ".join(f.short() if f.kind != "block" else "block tag %d/%d" % (f.tag, len(f.fields))
                      for f in self.fields[:8]))


class Reader:
    def __init__(self, data):
        self.d = data
        self.p = 0
        self.objs = []            # object table, in write order
        self.shared = set()       # object numbers reached through a shared pointer

    def u(self, n):
        v = int.from_bytes(self.d[self.p:self.p + n], "big")
        self.p += n
        return v

    def s(self, n):
        v = int.from_bytes(self.d[self.p:self.p + n], "big", signed=True)
        self.p += n
        return v

    def header(self):
        magic = self.u(4)
        if magic != MAGIC:
            raise ValueError("not a marshal stream: magic %08x" % magic)
        self.u(4)   # data length
        self.u(4)   # number of objects
        self.u(4)   # size32
        self.u(4)   # size64

    def read(self):
        c = self.d[self.p]
        self.p += 1
        if c >= 0x80:                                   # PREFIX_SMALL_BLOCK
            tag = c & 0xF
            size = (c >> 4) & 0x7
            return self.block(tag, size)
        if c >= 0x40:                                   # PREFIX_SMALL_INT
            return Node("int", value=c & 0x3F)
        if c >= 0x20:                                   # PREFIX_SMALL_STRING
            return self.string(c & 0x1F)
        if c == 0x00:
            return Node("int", value=self.s(1))
        if c == 0x01:
            return Node("int", value=self.s(2))
        if c == 0x02:
            return Node("int", value=self.s(4))
        if c == 0x03:
            return Node("int", value=self.s(8))
        if c in (0x04, 0x05, 0x06, 0x14):               # SHARED8/16/32/64
            n = {0x04: 1, 0x05: 2, 0x06: 4, 0x14: 8}[c]
            back = self.u(n)
            node = self.objs[len(self.objs) - back]
            self.shared.add(id(node))
            return node
        if c == 0x08:                                   # BLOCK32
            h = self.u(4)
            return self.block(h & 0xFF, h >> 10)
        if c == 0x13:                                   # BLOCK64
            h = self.u(8)
            return self.block(h & 0xFF, h >> 10)
        if c == 0x09:
            return self.string(self.u(1))
        if c == 0x0A:
            return self.string(self.u(4))
        if c == 0x15:
            return self.string(self.u(8))
        if c in (0x0B, 0x0C):                           # DOUBLE_BIG / DOUBLE_LITTLE
            raw = self.d[self.p:self.p + 8]
            self.p += 8
            node = Node("double", value=raw)
            self.objs.append(node)
            return node
        if c in (0x0D, 0x0E, 0x07, 0x0F):               # DOUBLE_ARRAY*
            n = self.u(1) if c in (0x0D, 0x0E) else self.u(4)
            raw = self.d[self.p:self.p + 8 * n]
            self.p += 8 * n
            node = Node("double", value=raw)
            self.objs.append(node)
            return node
        if c in (0x12, 0x18, 0x19):                     # CUSTOM / CUSTOM_LEN / CUSTOM_FIXED
            start = self.p
            while self.d[self.p] != 0:                  # the custom identifier
                self.p += 1
            ident = self.d[start:self.p]
            self.p += 1
            if c == 0x18:
                self.u(4)
                size = self.u(8)
            elif c == 0x19:
                size = None
            else:
                size = None
            if size is None:
                raise ValueError("custom block %r without a length at %d" % (ident, start))
            raw = self.d[self.p:self.p + size]
            self.p += size
            node = Node("custom", value=ident + b":" + raw)
            self.objs.append(node)
            return node
        raise ValueError("marshal code %#x at %d" % (c, self.p - 1))

    def string(self, n):
        v = self.d[self.p:self.p + n]
        self.p += n
        node = Node("string", value=v)
        self.objs.append(node)
        return node

    def block(self, tag, size):
        node = Node("block", tag=tag, fields=[])
        # A block of size 0 is an atom: the runtime does not put it in the
        # object table, so numbering it here would shift every shared pointer
        # after it (intern.c/extern.c: only non-atom blocks are registered).
        if size > 0:
            self.objs.append(node)                      # numbered before its fields
        for _ in range(size):
            node.fields.append(self.read())
        return node


def segments(data, what):
    table = int.from_bytes(data[8:16], "big")
    count = int.from_bytes(data[table:table + 4], "big")
    off, segs = table + 4, {}
    for _ in range(count):
        nlen = int.from_bytes(data[off:off + 4], "big")
        off += 4
        name = data[off:off + nlen].decode()
        off += nlen
        pos = int.from_bytes(data[off:off + 8], "big")
        length = int.from_bytes(data[off + 8:off + 16], "big")
        off += 32
        segs[name] = (pos, length)
    return segs


def load(path, seg):
    data = Path(path).read_bytes()
    pos, length = segments(data, path)[seg]
    r = Reader(data[pos:pos + length])
    r.header()
    root = r.read()
    return root, r


def compare(a, b, ra, rb, out, path="", seen=None):
    """Walk both trees together.  Record value differences and sharing differences."""
    if seen is None:
        seen = set()
    key = (id(a), id(b))
    if key in seen:
        return True
    seen.add(key)
    sa, sb = id(a) in ra.shared, id(b) in rb.shared
    if a.kind != b.kind or a.tag != b.tag or len(a.fields) != len(b.fields) or a.value != b.value:
        out["diff"].append((path, a.short(), b.short()))
        return False
    if sa != sb:
        out["sharing"].append((path, "replay" if sa else "stock", a.short()))
    ok = True
    for i, (x, y) in enumerate(zip(a.fields, b.fields)):
        ok &= compare(x, y, ra, rb, out, "%s.%d" % (path, i), seen)
    return ok


def walk(node, path):
    for part in [p for p in path.split(".") if p]:
        node = node.fields[int(part)]
    return node


def dump(node, depth, indent=""):
    if depth == 0 or node.kind != "block":
        return indent + node.short() + "\n"
    text = indent + "block tag %d, %d field(s)\n" % (node.tag, len(node.fields))
    for i, f in enumerate(node.fields):
        text += indent + " [%d] " % i + dump(f, depth - 1, indent + "  ").lstrip()
    return text


def main():
    sys.setrecursionlimit(1000000)
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    show = [a[len("--show="):] for a in sys.argv[1:] if a.startswith("--show=")]
    depth = next((int(a[len("--depth="):]) for a in sys.argv[1:] if a.startswith("--depth=")), 3)
    replay, stock = args[0], args[1]
    seg = args[2] if len(args) > 2 else "library"
    ra_root, ra = load(replay, seg)
    rb_root, rb = load(stock, seg)
    if show:
        for path in show:
            print("== path %s" % path)
            print("-- replay\n" + dump(walk(ra_root, path), depth))
            print("-- stock\n" + dump(walk(rb_root, path), depth))
        return
    out = {"diff": [], "sharing": []}
    equal = compare(ra_root, rb_root, ra, rb, out)
    print("segment %s: objects replay %d, stock %d" % (seg, len(ra.objs), len(rb.objs)))
    print("values equal: %s" % equal)
    for path, x, y in out["diff"][:20]:
        print("  VALUE DIFFERS at %s\n    replay: %s\n    stock : %s" % (path or "(root)", x, y))
    for path, who, short in out["sharing"][:20]:
        print("  SHARING DIFFERS at %s: only %s reached it through a shared pointer\n    node: %s"
              % (path or "(root)", who, short))
    print("%d value differences, %d sharing differences" % (len(out["diff"]), len(out["sharing"])))


if __name__ == "__main__":
    main()
