#!/usr/bin/env python3
"""Gate part 2 of BET-84: per-proof replay fixtures (dispatch://BET-119).

`run.sh` is the entry point, and this file is its command line.  The modules
beside it hold the logic:

    fixture_spec.py  a fixture's `expect.json`, checked and merged with the
                     defaults
    fixture.py       one fixture, run: its phases, assertions and modes
    rocq.py          the Rocq under test, and how its programs are run
    trees.py         a fixture's trees, and the files a compile writes
    records.py       the registration's records, published and read
    vo_compare.py    a replay `.vo` against stock's, and the one difference
                     that a fixture may excuse
    objfile.py       the segment table of a `.vo`

Exit status: 1 when a fixture failed, 0 otherwise.  A skipped fixture is
printed and does not fail the run: `--slow` was not given, a prerequisite is
missing, or the fixture's own `trigger_optional` did not fire.

Two half-runs exist for the time when no replay Rocq is built yet:
`--register-only` runs the registration and the record assertions, and
`--stock-control` compiles both grade trees with no replay option, which
exercises the exit-code, object and coqchk halves and states the box's
stock-against-stock noise.
"""

import argparse
import os
import sys
from pathlib import Path

from fixture import Fixture, probe
from fixture_spec import fixture_names, load_spec
from rocq import Rocq
from trees import open_dirs, remove_tree


def main(argv=None):
    ap = argparse.ArgumentParser(prog="run.sh", description=__doc__.splitlines()[0])
    ap.add_argument("bindir", nargs="?", help="the directory holding rocq and rocqchk")
    ap.add_argument("outdir", nargs="?", help="where the trees, logs and objects go")
    ap.add_argument("--only", action="append", default=[], metavar="FIXTURE")
    ap.add_argument("--list", action="store_true", help="name every fixture and exit")
    ap.add_argument("--register-only", action="store_true",
                    help="run only the original-tree -proof-record registration and record assertions")
    ap.add_argument("--stock-control", action="store_true",
                    help="compile both grade trees with no replay option: the object comparison and coqchk "
                         "halves, and the box's stock-against-stock noise")
    ap.add_argument("--slow", action="store_true", help="also run the fixtures that take minutes")
    ap.add_argument("--segcmp", default=os.environ.get("SEGCMP_NORM"),
                    help="lane R1's segcmp_norm, built; without it the comparison is in Python")
    args = ap.parse_args(argv)

    names = fixture_names()
    if args.only:
        unknown = [n for n in args.only if n not in names]
        if unknown:
            raise SystemExit("no such fixture: %s" % ", ".join(unknown))
        names = [n for n in names if n in args.only]

    if args.list:
        for name in names:
            try:
                spec = load_spec(name)
            except ValueError as exc:
                raise SystemExit(str(exc))
            mark = " [slow]" if spec["slow"] else ""
            print("%-28s%s %s" % (name, mark, spec["doc"]))
        return 0

    if not args.bindir or not args.outdir:
        ap.error("the rocq bin directory and an output directory are required")

    rocq = Rocq(args.bindir)
    out = Path(args.outdir).resolve()
    out.mkdir(parents=True, exist_ok=True)
    segcmp = Path(args.segcmp).resolve() if args.segcmp else None
    if segcmp and not segcmp.exists():
        raise SystemExit("no segcmp_norm at %s" % segcmp)

    failed, skipped, passed = [], [], []
    for name in names:
        try:
            spec = load_spec(name)
        except ValueError as exc:  # a broken expect.json fails its fixture
            print("FAIL %s: %s" % (name, exc), flush=True)
            failed.append(name)
            continue
        if spec["slow"] and not args.slow:
            print("SKIP %s: slow; pass --slow" % name, flush=True)
            skipped.append(name)
            continue
        why = None
        for what in spec["requires"]:
            why = probe(rocq, spec, out, what)
            if why:
                break
        if why:
            print("SKIP %s: %s" % (name, why), flush=True)
            skipped.append(name)
            continue
        work = out / name
        if work.exists():
            remove_tree(work)
        work.mkdir(parents=True)
        fix = Fixture(spec, rocq, work, segcmp)
        try:
            fix.run(register_only=args.register_only, stock_control=args.stock_control)
        except Exception as exc:  # a broken fixture is a failure, not a crash
            fix.fail("the runner raised %s: %s" % (type(exc).__name__, exc))
        finally:
            # The read-only record directories would stop `rm -rf` of the
            # output directory (`make clean`).
            open_dirs(work)
        notes = (" | " + "; ".join(fix.notes)) if fix.notes else ""
        if fix.bad:
            print("FAIL %s: %s%s" % (name, "; ".join(fix.bad), notes), flush=True)
            failed.append(name)
        elif fix.skip:
            print("SKIP %s: %s%s" % (name, fix.skip, notes), flush=True)
            skipped.append(name)
        else:
            print("PASS %s%s" % (name, notes), flush=True)
            passed.append(name)

    print("%d passed, %d failed, %d skipped" % (len(passed), len(failed), len(skipped)))
    if failed:
        print("failed: %s" % ", ".join(failed))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
