#!/usr/bin/env python3
"""One value per recorded channel (BET-84 P3).

A proof's record holds, for each read, the value the lookup gave. Replay
accepts a stored term only when every recorded read gives that same value
now. So two pieces of code hold the value of one channel: the recorder, at
the lookup, and the replay evaluator that checks the record again. If they
compute it in two different ways they can disagree, and a replay can accept
an input that changed.

That is not hypothetical. On 2026-10-25 the recorder digested a constant of
a required library by the library's digest while the evaluator digested its
body, and every proof of the smoke file missed. A silent version of the same
mistake accepts a changed input instead of refusing it.

**The rule.** A channel that has a replay evaluator computes its value in
exactly ONE function, which both sides call. A channel with no evaluator is
not a soundness risk, because every proof that reads it misses; those are
listed, not failed, so the next evaluator to write is visible.

The check pairs the two sides by channel, and a channel is named three ways
in this tree, all of which are followed:

* a string literal, at the record site and in `register_evaluator`;
* an identifier bound in the same file (`library/nametab.ml` builds one
  channel per nametab from its summary name);
* a parameter of a local helper (`kernel/environ.ml`'s `Recorded.once`,
  `plugins/ltac/tacenv.ml`'s `record`), whose callers pass the literal. The
  caller's value expression is the one that counts, and it is collected from
  every call that passes `~channel:`, not only from calls to
  `Proof_recorder.read`.

Run: dev/tools/census/replay_channels.py [--root DIR] [--quiet]
Exit 0 when every evaluated channel has a single implementation, 1 otherwise.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

#: A call that names a channel: the recorder's own `read`/`read_by`, or any
#: helper call that passes one on.
CHANNEL_CALL = re.compile(r"~channel:(\"[^\"]*\"|[A-Za-z_][\w.']*)")
#: OCaml label punning: `~channel` with no value, so the name is the
#: enclosing helper's parameter and its callers supply it.
CHANNEL_PUN = re.compile(r"~channel(?![:\w])")
#: Only a qualified call registers an evaluator; the unqualified one is the
#: definition in `lib/proof_replay.ml`.
EVALUATOR = re.compile(
    r"(?:Proof_replay|Replay)\.register_evaluator\s+(\"[^\"]*\"|[A-Za-z_][\w.']*)(?=[\s(])",
)
#: The `let` that encloses a punned site, so its callers can be found.
ENCLOSING_LET = re.compile(r"^\s*let\s+(?:rec\s+)?([a-z_][\w']*)", re.M)
#: A function that computes a channel's value for both sides. By convention
#: it is named `recorded_*`; the two whole-table providers and the kernel's
#: own per-channel helpers are named here because they predate it.
SHARED = re.compile(r"\b(recorded_\w+|of_value|of_rules|start_reads|table_reads|record_hook)\b")
#: Computing a digest on the spot.
INLINE = re.compile(r"\b(Proof_recorder\.digest\w*|Proof_record\.digest_value|Digest\.|Marshal\.)")

#: The build tree holds copies, and the test suite holds the fixtures that
#: exercise this rule on purpose.
SKIP_DIRS = ("_build", "test-suite")


def files(root: pathlib.Path):
    for path in sorted(root.rglob("*.ml")):
        if any(part in SKIP_DIRS for part in path.parts):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        if "~channel:" in text or "register_evaluator" in text:
            yield path, text


def window(text: str, at: int, span: int = 420) -> str:
    """One call's own text.

    A fixed span would leak into the next function and borrow its value
    function, which hides a second implementation. So the text stops where
    the parentheses opened since [at] have all closed and a new top-level
    `let` begins, whichever comes first.
    """
    depth, out = 0, []
    for ch in text[at:at + span]:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                break
        out.append(ch)
        if depth == 0 and "".join(out[-5:]).endswith("\nlet "):
            break
    return "".join(out)


def registration_block(text: str, at: int, back: int = 4000, span: int = 4000) -> str:
    """The `let () = ...` an evaluator is registered in.

    An evaluator rarely digests in its own parentheses. `library/nametab.ml`
    registers `on qualid (fun qid -> Tab.locate qid !the_tab)` and keeps the
    digest in a sibling `let value` of the same block, so a check that reads
    only the call's own text sees nothing. The block is what must hold one
    value function, so the block is what is classified.
    """
    start = text.rfind("let () =", max(0, at - back), at)
    if start < 0:
        return window(text, at)
    indent = len(text[:start].split("\n")[-1])
    out = []
    for line in text[start:at + span].split("\n"):
        if out and line.strip().startswith("let ") and len(line) - len(line.lstrip()) <= indent:
            break
        out.append(line)
    return "\n".join(out)


def token(expr: str) -> str:
    return expr.strip('"') if expr.startswith('"') else expr


def classify(expr: str, text: str = ""):
    """(shared value functions named, computes a digest itself).

    A record site that calls its file's `record_hook` names, through it,
    whatever value functions the hook is set to: `plugins/ltac/tacenv.ml`
    installs one hook that dispatches to its two `recorded_*` functions.
    """
    shared = set(SHARED.findall(expr))
    if "record_hook" in shared and text:
        hook = re.search(r"record_hook\s*:=(.{0,600})", text, re.S)
        if hook:
            shared |= set(SHARED.findall(hook.group(1)))
    return shared, bool(INLINE.search(expr)) and not SHARED.search(expr)


def enclosing_let(text: str, at: int) -> str | None:
    """The name of the `let` a punned site sits in."""
    lets = [m.group(1) for m in ENCLOSING_LET.finditer(text, 0, at)]
    return lets[-1] if lets else None


def helper_channels(text: str, helper: str):
    """The channels the callers of a punned helper pass it, labelled or not."""
    found = set()
    call = re.compile(r"\b%s\b\s+(?:~channel:)?(\"[^\"]*\"|[a-z_][\w']*)" % re.escape(helper))
    for m in call.finditer(text):
        name = m.group(1)
        # A caller passes a literal, or an identifier bound to one in this
        # file (nametab builds one channel name per nametab).
        if name.startswith('"') or re.search(r"\blet\s+%s\s*=" % re.escape(name.strip('"')), text):
            found.add(token(name))
    return found


def scan(root: pathlib.Path):
    record, evaluated, dynamic = {}, {}, set()
    for path, text in files(root):
        for m in CHANNEL_CALL.finditer(text):
            name = token(m.group(1))
            if not m.group(1).startswith('"'):
                dynamic.add(name)
            line = text[: m.start()].count("\n") + 1
            shared, inline = classify(window(text, m.start()), text)
            record.setdefault(name, []).append(("%s:%d" % (path, line), shared, inline))
        for m in CHANNEL_PUN.finditer(text):
            helper = enclosing_let(text, m.start())
            if helper is None:
                continue
            line = text[: m.start()].count("\n") + 1
            # The value this site records is computed in the helper's own
            # body, which is where a second implementation would hide.
            shared, inline = classify(window(text, m.start()), text)
            for name in helper_channels(text, helper):
                dynamic.add(name)
                record.setdefault(name, []).append(("%s:%d" % (path, line), shared, inline))
        for m in EVALUATOR.finditer(text):
            name = token(m.group(1))
            if not m.group(1).startswith('"'):
                dynamic.add(name)
            line = text[: m.start()].count("\n") + 1
            shared, inline = classify(registration_block(text, m.start()), text)
            evaluated[name] = ("%s:%d" % (path, line), shared, inline)
    return record, evaluated, dynamic


def check(root: pathlib.Path):
    record, evaluated, dynamic = scan(root)
    problems = []
    for name, (where, ev_shared, ev_inline) in sorted(evaluated.items()):
        sites = record.get(name, [])
        if not sites:
            problems.append("%s: channel %s has an evaluator and no record site; "
                            "its name cannot be paired, so the two sides are unchecked" % (where, name))
            continue
        if ev_inline:
            problems.append("%s: channel %s has a replay evaluator that computes its value itself; "
                            "it must call the one value function the record site calls" % (where, name))
        rec_shared = set()
        for site, shared, inline in sites:
            if inline:
                problems.append("%s: channel %s has a replay evaluator and digests its value here too"
                                % (site, name))
            rec_shared |= shared
        if ev_shared and rec_shared and not (ev_shared & rec_shared):
            problems.append("%s: channel %s is computed by %s here and by %s at its record site: "
                            "two implementations" % (where, name, sorted(ev_shared), sorted(rec_shared)))
    return record, evaluated, dynamic, problems


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".", type=pathlib.Path)
    ap.add_argument("--quiet", action="store_true", help="only the verdict and the failures")
    args = ap.parse_args()
    record, evaluated, dynamic, problems = check(args.root)

    if not args.quiet:
        paired = sorted(set(evaluated) & set(record))
        print("channels recorded: %d (%d named by an identifier), with an evaluator: %d"
              % (len(record), len(dynamic & set(record)), len(paired)))
        missing = sorted(c for c in record if c not in evaluated)
        if missing:
            print("no evaluator yet (every proof that reads one misses): " + ", ".join(missing))
    if problems:
        print("ONE VALUE PER CHANNEL: %d violation(s)" % len(problems))
        for p in problems:
            print("  " + p)
        return 1
    print("one value per channel: every evaluated channel has a single implementation")
    return 0


if __name__ == "__main__":
    sys.exit(main())
