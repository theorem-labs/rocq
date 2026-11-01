"""A replay `.vo` against stock's, and the one difference that a fixture may
excuse (BET-84).

The `.vo` comparison follows lane R1's rule
(`scripts/speed_loop/lanes/r1/segcmp_norm.ml` in a grading-harness
checkout): the `vmlibrary` segment by value, every other segment by bytes.
Two stock compiles of one source can write equal `vmlibrary` values with a
different Marshal sharing, so bytes do not decide that segment.  With
`--segcmp PATH` (or `SEGCMP_NORM` in the environment) the runner calls that
program with `--every-segment`, which is the rule itself.  Without it the
runner compares the segments in Python, by the MD5 the segment table records,
and a `vmlibrary`-only difference is reported as `vmlibrary_bytes` -- a
difference it cannot decide, so it counts as a failure and the line says so.
"""

import subprocess
import sys
from pathlib import Path

from objfile import segments

HERE = Path(__file__).resolve().parent


def compare_vo_python(a, b):
    """Differing segment names, by the MD5 the segment table records.

    The `vmlibrary` segment is compared by bytes here, which the lane's rule
    does not: two stock compiles can write the same value with another
    sharing.  Such a difference is reported as `vmlibrary_bytes`, and the
    caller says that only `segcmp_norm` can decide it.
    """
    da, db = a.read_bytes(), b.read_bytes()
    if da == db:
        return []
    sa, sb = segments(da, a.name), segments(db, b.name)
    bad = []
    for name in list(sa) + [n for n in sb if n not in sa]:
        if name not in sa or name not in sb:
            bad.append(name + "_missing")
            continue
        pa, la, ha = sa[name]
        pb, lb, hb = sb[name]
        if ha != hb or da[pa:pa + la] != db[pb:pb + lb]:
            bad.append("vmlibrary_bytes" if name == "vmlibrary" else name)
    if not bad:
        bad.append("outside every segment")
    return bad


def compare_trees_segcmp(segcmp, listing, a, b, work):
    """Lane R1's rule itself: segcmp_norm --every-segment."""
    lst = work / "segcmp-list.txt"
    lst.write_text("".join(x + "\n" for x in listing))
    p = subprocess.run([str(segcmp), "--every-segment", str(lst), str(a), str(b)],
                       capture_output=True, text=True)
    if p.returncode != 0:
        return None, "segcmp_norm exited %d: %s" % (p.returncode, (p.stdout + p.stderr).strip()[:400])
    diffs = {}
    for line in p.stdout.splitlines():
        parts = line.split(None, 2)
        if parts and parts[0] == "diff":
            diffs[parts[1]] = parts[2] if len(parts) > 2 else ""
    return diffs, None


#: The only fixtures whose object difference may be excused, named one by
#: one. GRADE retired byte identity as a correctness gate on 2026-10-26, so
#: a Marshal sharing difference is a reuse-rate item; everything else is a
#: failure, and an unlisted fixture is never excused whatever its
#: `expect.json` says. channels_unchanged replays five proofs whose terms
#: name bool and nat, and its library segment shares the string "Datatypes"
#: where stock's does (vodiff, 2026-10-26: 0 value differences, 2 sharing
#: differences, every other segment equal). write_scheme_rewrite replays
#: two proofs whose stored terms carry the scheme they created, and its
#: library segment shares "A" and "PR" where stock's does (vodiff,
#: 2026-10-30: 0 value differences, 4 sharing differences). vm_lia_hit
#: replays two lia proofs whose terms name Stdlib's BinInt, and stock's
#: library segment reaches the string "BinInt" through a shared pointer
#: where the replay's does not (vodiff, 2026-10-30: 0 value differences,
#: 2 sharing differences; the same on a switch built before the vm_global
#: read). micromega_cache_blocked replays a nia and a lia proof over Z, with
#: the same two "BinInt" sharing differences (vodiff, 2026-10-31, a build of
#: e560ab16e4: 0 value differences, 2 sharing differences, opaques and
#: vmlibrary equal).
#: eval_abbreviation, eval_notation and eval_prim_token share the
#: string "Datatypes" where stock does, and eval_ltac2_global,
#: eval_ltac2_notation, ltac_alias_moved and ltac_redef_moved share
#: "Logic" (vodiff, 2026-10-31, a build of 481ab9697f with
#: 9.2/library-is-loaded: 0 value differences, 1 or 2 sharing differences,
#: opaques and vmlibrary equal). Their sharing depends on the Corelib .vo
#: files and the load path: the same rocq writes equal bytes with the
#: Corelib of the lane switch (466ade62 base), and not with a Corelib built
#: from this tree; there the four "Logic" fixtures write equal bytes only
#: when Stdlib is installed beside Corelib, as in the CI job.
#: eval_option_tables shares "Datatypes" the same way (vodiff, 2026-10-31,
#: a build of 6ef3d08b1a: 0 value differences, 2 sharing differences,
#: opaques and vmlibrary equal).
EXEMPTIBLE_FIXTURES = ("place_same_file", "hint_removed", "channels_unchanged", "write_scheme_rewrite",
                       "vm_lia_hit", "micromega_cache_blocked", "eval_abbreviation", "eval_notation",
                       "eval_prim_token", "eval_ltac2_global", "eval_ltac2_notation", "ltac_alias_moved",
                       "ltac_redef_moved", "eval_option_tables")


def exemption_allowed(fixture, differing_segments, library_values_equal):
    """May this object difference be excused? (allowed, reason).

    Every condition must hold: the fixture is on the list above, the ONLY
    segment that differs is `library`, and that segment's decoded values are
    equal, so the difference is Marshal sharing alone. A differing value, a
    difference in any other segment, or an unlisted fixture fails.

    This is a pure function so the conditions can be tested directly, with
    no `.vo` to forge: see test_vo_exempt.py. The first version keyed on the
    file name alone and would have excused a value difference in another
    segment (XP3's P1 at 7cb123ab61).
    """
    if fixture not in EXEMPTIBLE_FIXTURES:
        return False, "fixture %s is not on the exemptible list" % fixture
    if sorted(differing_segments) != ["library"]:
        return False, ("the differing segments are %s, and only a library-only difference may be excused"
                       % (sorted(differing_segments) or ["none"]))
    if not library_values_equal:
        return False, "the library segment's VALUES differ, which is never excusable"
    return True, "library values equal; Marshal sharing alone"


def library_values_equal(va, vb):
    """Does the library segment hold the same VALUE in the objects `va` and `vb`?

    Only `vodiff.py` can tell a value difference from a sharing one: it
    decodes the Marshal stream and resolves its shared pointers.
    """
    tool = HERE / "vodiff.py"
    p = subprocess.run([sys.executable, str(tool), str(va), str(vb), "library"],
                       capture_output=True, text=True)
    lines = [l for l in p.stdout.splitlines() if "value differences" in l]
    return bool(lines) and lines[-1].startswith("0 value differences")
