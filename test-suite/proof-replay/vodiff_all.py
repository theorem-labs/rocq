#!/usr/bin/env python3
"""vodiff_all.py VODIFF REPLAY.vo STOCK.vo SEGMENT -- runs on speed-r1 (BET-84 P3, lane design "d").

The branch's vodiff.py prints at most 20 value differences per segment. This imports it unchanged and calls its own
load() and compare() to list EVERY value difference, then tells which are dependency digests: a 16-byte string
equal, on each side, to the library-segment MD5 of a .vo in that side's tree (found by walking up from the object
to the `rocq` root and hashing every .vo under it). Prints JSON: counts, the digest differences with the library
they name, and every other value difference.
"""

import hashlib
import importlib.util
import json
import sys
from pathlib import Path

# argv: [VODIFF] REPLAY.vo STOCK.vo SEGMENT.  Outside the suite (a sweep on a lane box) vodiff.py may live
# elsewhere, so the path stays overridable; inside the suite the sibling is the one to use.
args = sys.argv[1:]
vodiff_path = Path(args.pop(0)) if len(args) == 4 else Path(__file__).resolve().parent / "vodiff.py"
if len(args) != 3:
    raise SystemExit("usage: vodiff_all.py [VODIFF] REPLAY.vo STOCK.vo SEGMENT")
spec = importlib.util.spec_from_file_location("vodiff", vodiff_path)
vodiff = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vodiff)
replay, stock, segment = Path(args[0]), Path(args[1]), args[2]
sys.setrecursionlimit(1_000_000)


def tree_root(p: Path) -> Path:
    """The directory to search for the object a dependency digest names.

    On a lane box the objects sit under a `rocq/` checkout, which is the whole
    search space.  A fixture's objects do not, so fall back to the highest
    ancestor that still holds `.vo` files: that is the fixture's own tree, and
    searching wider would only slow the sweep down.
    """
    for parent in p.parents:
        if parent.name == "rocq":
            return parent
    root = p.parent
    for parent in p.parents:
        if any(parent.glob("*.vo")) or any(parent.glob("*/*.vo")):
            root = parent
    return root


def library_md5s(root: Path) -> dict[bytes, str]:
    out = {}
    for vo in root.rglob("*.vo"):
        data = vo.read_bytes()
        try:
            pos, length = vodiff.segments(data, vo)["library"]
        except (KeyError, IndexError, ValueError):
            continue
        out[hashlib.md5(data[pos : pos + length]).digest()] = str(vo.relative_to(root))
    return out


ra_root, ra = vodiff.load(replay, segment)
rb_root, rb = vodiff.load(stock, segment)
out = {"diff": [], "sharing": []}
equal = vodiff.compare(ra_root, rb_root, ra, rb, out)
mine, theirs = library_md5s(tree_root(replay)), library_md5s(tree_root(stock))
digests, other = [], []
for path, x, y in out["diff"]:
    a = vodiff.walk(ra_root, path) if path else ra_root
    b = vodiff.walk(rb_root, path) if path else rb_root
    if a.kind == b.kind == "string" and len(a.value) == len(b.value) == 16 and mine.get(a.value) and (
        mine.get(a.value) == theirs.get(b.value)
    ):
        digests.append({"path": path, "library": mine[a.value]})
    else:
        other.append({"path": path, "replay": x, "stock": y})
print(json.dumps({"segment": segment, "values_equal": equal, "value_differences": len(out["diff"]),
                  "sharing_differences": len(out["sharing"]), "dependency_digests": digests,
                  "unexplained": other}, indent=1))
