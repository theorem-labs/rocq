#!/usr/bin/env python3
"""One value per recorded channel (BET-84 P3).

A proof's record holds, for each read, the value the lookup gave. Replay
accepts a stored term only when every recorded read gives that same value
now. So two pieces of code hold the value of one channel: the recorder, at
the lookup, and the replay evaluator that checks the record again. If they
compute it in two different ways they can disagree, and a replay can
accept an input that changed. That is the defect this check exists for: on
2026-10-25 the recorder digested a constant of a required library by the
library's digest while the evaluator digested its body, and every proof of
the smoke file missed. A silent version of the same mistake accepts a
changed input instead of refusing it.

The rule: a channel that has a replay evaluator computes its value in
exactly ONE function, which both sides call. A channel with no evaluator
is not a soundness risk, because every proof that reads it misses; those
are listed, not failed, so the next evaluator to write is visible.

Run: dev/tools/census/replay_channels.py [--root DIR] [--quiet]
Exit 0 when every evaluated channel has one implementation, 1 otherwise.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

RECORD = re.compile(
    r"Proof_recorder\.read(?:_by)?\s+(?P<args>(?:~\w+:(?:\([^()]*(?:\([^()]*\)[^()]*)*\)|\"[^\"]*\"|[\w.!]+)\s*)+)",
    re.S,
)
EVALUATOR = re.compile(r"Proof_replay\.register_evaluator\s+(?P<chan>\"[^\"]*\")")
#: A value expression that calls a shared per-channel function, or a
#: provider's own list. Anything else computes the value on the spot.
SHARED = re.compile(r"\b(recorded_\w+|of_value|of_rules|start_reads|table_reads)\b")
#: A value expression that digests something itself.
INLINE = re.compile(r"Proof_recorder\.digest")


def field(args: str, name: str) -> str | None:
    pattern = r"~%s:(\([^()]*(?:\([^()]*\)[^()]*)*\)|\"[^\"]*\"|[\w.]+)" % name
    m = re.search(pattern, args, re.S)
    return m.group(1) if m else None


def scan(root: pathlib.Path):
    """Returns (record sites by channel, channels with an evaluator)."""
    sites: dict[str, list[tuple[str, bool]]] = {}
    evaluated: set[str] = set()
    for path in sorted(root.rglob("*.ml")):
        if "_build" in path.parts or "test-suite" in path.parts:
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        if "Proof_recorder.read" not in text and "register_evaluator" not in text:
            continue
        for m in EVALUATOR.finditer(text):
            evaluated.add(m.group("chan").strip('"'))
        for m in RECORD.finditer(text):
            args = m.group("args")
            chan, value = field(args, "channel"), field(args, "value")
            if chan is None or value is None or not chan.startswith('"'):
                # A channel built at run time (the nametab functor names one
                # per table) is its module's own; it has no second site.
                continue
            line = text[: m.start()].count("\n") + 1
            inline = bool(INLINE.search(value)) and not SHARED.search(value)
            sites.setdefault(chan.strip('"'), []).append(("%s:%d" % (path, line), inline))
    return sites, evaluated


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".", type=pathlib.Path)
    ap.add_argument("--quiet", action="store_true", help="only the verdict and the failures")
    args = ap.parse_args()
    sites, evaluated = scan(args.root)

    problems = []
    for chan in sorted(evaluated):
        for where, inline in sites.get(chan, []):
            if inline:
                problems.append("%s: channel %s has a replay evaluator and digests its value here too" % (where, chan))

    if not args.quiet:
        missing = sorted(c for c in sites if c not in evaluated)
        print("channels recorded: %d, with an evaluator: %d" % (len(sites), len(evaluated & set(sites))))
        if missing:
            print("no evaluator yet (every proof that reads one misses): " + ", ".join(missing))
    if problems:
        print("ONE VALUE PER CHANNEL: %d site(s) compute an evaluated channel's value a second way" % len(problems))
        for p in problems:
            print("  " + p)
        return 1
    print("one value per channel: every evaluated channel has a single implementation")
    return 0


if __name__ == "__main__":
    sys.exit(main())
