#!/usr/bin/env python3
"""Gate part 2 of BET-84: per-proof replay fixtures (dispatch://BET-119).

`run.sh` is the entry point; this file holds the logic.  One fixture is a tiny
Rocq project in two versions, `original/` and `edited/`, plus `expect.json`.
For one fixture the runner does, in order:

1.  **Registration.**  Compile `original/` with `rocq compile -proof-record`.
    Every file must compile, and every file must leave its record beside the
    `.vo` (`Proof_record.path_of_vo`).  The records are collected into one
    directory, under the names `-proof-replay-dir` looks for: the dotted
    logical library name, and the same name with the dots turned into slashes
    (`record_layout` chooses which of the two the fixture publishes).
2.  **Record assertions.**  `expect.json`'s `records` says, per proof, what the
    registration must have stored: the ineligibility reasons it must carry,
    and whether it may hold a stored term (`replay`).
3.  **The grade.**  Compile `edited/` in the tree `a/` with
    `-proof-replay-dir <records> -proof-replay-ratio <r>` (`-proof-replay
    <records>/<replay_file>` when the fixture names one), read each
    `<base>.proof-replay.json` and check it against `summaries`.
4.  **Stock.**  Compile `edited/` again in the tree `b/` with no replay option.
    The two runs must agree: the same exit code per file, and for a file that
    compiled, the same `.vo`.
5.  **coqchk.**  `rocqchk` over the replay run's objects must accept them.

The `.vo` comparison follows lane R1's rule
(`scripts/speed_loop/lanes/r1/segcmp_norm.ml` in a binary-equivalence-taiga
checkout): the `vmlibrary` segment by value, every other segment by bytes.
Two stock compiles of one source can write equal `vmlibrary` values with a
different Marshal sharing, so bytes do not decide that segment.  With
`--segcmp PATH` (or `SEGCMP_NORM` in the environment) the runner calls that
program with `--every-segment`, which is the rule itself.  Without it the
runner compares the segments in Python, by the MD5 the segment table records,
and a `vmlibrary`-only difference is reported as `vmlibrary_bytes` -- a
difference it cannot decide, so it counts as a failure and the line says so.
`a/` and `b/` are one character each because an object's `vmlibrary` bytes
depend on the length of the build path.

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
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
import pathlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURES = HERE / "fixtures"
MISS_KINDS = ("key", "read", "ineligible", "missing_record")

DEFAULTS = {
    "doc": "",
    "root": "PR",
    "mode": "replay",
    "slow": False,
    "requires": [],
    "native_compiler": "no",
    "common_flags": [],
    "register_flags": [],
    "grade_flags": [],
    "replay_extra_flags": [],
    # One record file under the records directory, given to `-proof-replay`
    # in place of `-proof-replay-dir` (`Fixture.replay_flags`).
    "replay_file": None,
    "ratio": "1",
    # Lane R1 measured that the stack limit changes the bytes of a `.vo`, so a
    # fixture's compiles must all run under the limit a grade runs under, and
    # not under whatever the caller's shell happens to have.  8192 kB is the
    # limit the grading engine sets (BET-84 spec, "Resource limits").
    "stack_kb": 8192,
    "record_layout": "both",
    # Files the registration records but whose record is not published: the
    # grade finds no record for them under `-proof-replay-dir`.
    "unpublished": [],
    "compile_fails": [],
    "summaries": {},
    "records": {},
    "compare_stdout": [],
    "compare_stderr": [],
    "stdout_contains": {},
    "stderr_contains": {},
    "vo_exempt": {},
    "coqchk": True,
    "budget": None,
    "replay_wall_max": None,
    "usage": None,
    "mixed": None,
    "trigger_optional": None,
}


def fixture_names():
    return sorted(p.name for p in FIXTURES.iterdir() if (p / "expect.json").is_file())


def load_spec(name):
    spec = dict(DEFAULTS)
    spec.update(json.loads((FIXTURES / name / "expect.json").read_text()))
    spec["name"] = name
    return spec


# ---------------------------------------------------------------- the compiler


class Rocq:
    """The Rocq under test, as a bin directory.

    The caller's environment is passed through: a Rocq built with dune needs
    ROCQLIB, ROCQRUNTIMELIB and OCAMLPATH, and only the caller knows them.
    """

    def __init__(self, bindir):
        self.bin = Path(bindir).resolve()
        self.env = dict(os.environ)
        self.env["PATH"] = "%s:%s" % (self.bin, self.env.get("PATH", ""))
        for name in ("rocq", "rocqchk"):
            if not (self.bin / name).exists():
                raise SystemExit("no %s in %s" % (name, self.bin))
        # Every compile runs under the fixture's stack limit, so a missing
        # prlimit is a broken environment, not a reason to compare objects
        # made under two different limits.
        if not shutil.which("prlimit"):
            raise SystemExit("no prlimit in PATH: the compiles cannot be given their stack limit")

    def run(self, argv, cwd, timeout_s=None):
        if timeout_s is not None:
            argv = ["timeout", str(timeout_s)] + argv
        t0 = time.time()
        p = subprocess.run(argv, cwd=str(cwd), env=self.env, capture_output=True, text=True)
        return {
            "argv": argv,
            "rc": p.returncode,
            "out": p.stdout,
            "err": p.stderr,
            "wall": round(time.time() - t0, 3),
        }

    def compile(self, spec, cwd, flags, src, timeout_s=None):
        argv = [str(self.bin / "rocq"), "compile", "-q",
                "-native-compiler", spec["native_compiler"],
                "-Q", ".", spec["root"]]
        argv += spec["common_flags"] + flags + [src]
        if spec.get("stack_kb") is not None:
            argv = ["prlimit", "--stack=%d" % (int(spec["stack_kb"]) * 1024), "--"] + argv
        return self.run(argv, cwd, timeout_s)

    def coqchk(self, spec, cwd, libs):
        argv = [str(self.bin / "rocqchk"), "-silent", "-Q", ".", spec["root"]] + libs
        return self.run(argv, cwd)


# ------------------------------------------------------------------- the trees


def copy_tree(src, dst):
    if dst.exists():
        shutil.rmtree(dst)
    shutil.copytree(src, dst)


def lib_name(spec, src):
    return spec["root"] + "." + src[:-2].replace("/", ".")


def record_src(tree, src):
    return tree / (src[:-2] + ".proof-record.jsonl")


def summary_src(tree, src):
    return tree / (src[:-2] + ".proof-replay.json")


def vo_src(tree, src):
    return tree / (src[:-2] + ".vo")


def opaques_span(data, what):
    """(position, length) of the `opaques` segment of a .vo's bytes."""
    seg = segments(data, what).get("opaques")
    if seg is None:
        raise ValueError("%s: no opaques segment" % what)
    return seg[0], seg[1]


def publish_records(spec, reg, records):
    """The registration's records, under the names -proof-replay-dir reads.

    Each record's `.vo` is published beside it under the same name, as a
    registration tree holds it: a record made with `-proof-record-vo-ref`
    refers to the opaque proofs of that object.  `vo_mutation` then removes
    those objects (`remove`), or changes one byte inside their opaque proofs
    (`change`), so a fixture can show what a referring proof does without
    the object it was registered with.
    """
    published = []
    objects = []
    for src in spec["files"]:
        rec = record_src(reg, src)
        if not rec.is_file():
            return None, "registration wrote no record for %s" % src
        if src in spec["unpublished"]:
            continue
        name = lib_name(spec, src)
        targets = []
        if spec["record_layout"] in ("dotted", "both"):
            targets.append(records / (name + ".proof-record.jsonl"))
        if spec["record_layout"] in ("slashed", "both"):
            targets.append(records / (name.replace(".", "/") + ".proof-record.jsonl"))
        for target in targets:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(rec, target)
            published.append(target)
            obj = Path(str(target)[:-len(".proof-record.jsonl")] + ".vo")
            shutil.copyfile(vo_src(reg, src), obj)
            objects.append(obj)
    mutation = spec.get("vo_mutation")
    for obj in objects:
        if mutation == "remove":
            obj.unlink()
            continue
        if mutation == "change":
            data = bytearray(obj.read_bytes())
            try:
                pos, length = opaques_span(bytes(data), obj.name)
            except ValueError as exc:
                return None, str(exc)
            data[pos + length // 2] ^= 0xFF
            obj.write_bytes(bytes(data))
        elif mutation is not None:
            return None, "unknown vo_mutation %r" % mutation
        os.chmod(obj, 0o444)
    # `record_patch` sets one recorded read's value before the digest is
    # taken, so a fixture can hold a record no registration of its tree would
    # write (a null read inside an open section, say) and still be bound.
    for patch in spec.get("record_patch", []):
        for path in published:
            lines = path.read_text().splitlines()
            hit = False
            for k, line in enumerate(lines):
                entry = json.loads(line)
                if entry.get("kind") == "proof" and entry.get("name") == patch["proof"]:
                    for read in entry.get("reads", []):
                        if read.get("channel") == patch["channel"] and read.get("key") == patch["key"]:
                            read["value"] = patch["value"]
                            hit = True
                    lines[k] = json.dumps(entry, separators=(",", ":"))
            if not hit:
                return None, "record_patch matched no read: %r" % (patch,)
            path.write_text("".join(l + "\n" for l in lines))
    # A record the compiling user can write is refused, and so is one with no
    # digest to check it against (P3Deep F1, P3Bugs): a registration publishes
    # its records read-only with their SHA-256 beside them, so the fixtures do.
    for path in published:
        side = Path(str(path) + ".sha256")
        side.write_text(hashlib.sha256(path.read_bytes()).hexdigest() + "\n")
        os.chmod(side, 0o444)
        os.chmod(path, 0o444)
    return published, None


def parse_record(path):
    """The record file as (header, [proof...], trailer).  Raises ValueError."""
    header, proofs, trailer = None, [], None
    for n, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip():
            raise ValueError("%s:%d: empty line" % (path.name, n))
        obj = json.loads(line)
        kind = obj.get("kind")
        if kind == "header":
            if header is not None or proofs or trailer is not None:
                raise ValueError("%s:%d: a second header" % (path.name, n))
            header = obj
        elif kind == "proof":
            if header is None or trailer is not None:
                raise ValueError("%s:%d: a proof outside the file's body" % (path.name, n))
            proofs.append(obj)
        elif kind == "trailer":
            if trailer is not None:
                raise ValueError("%s:%d: a second trailer" % (path.name, n))
            trailer = obj
        else:
            raise ValueError("%s:%d: kind %r" % (path.name, n, kind))
    if header is None or trailer is None:
        raise ValueError("%s: no header or no trailer" % path.name)
    if trailer.get("proof_count") != len(proofs):
        raise ValueError("%s: proof_count %r against %d proof lines"
                         % (path.name, trailer.get("proof_count"), len(proofs)))
    return header, proofs, trailer


# ------------------------------------------------------- comparing the objects


def segments(data, what):
    """The segment table of a .vo (lib/objFile.ml): name -> (pos, len, md5)."""
    if len(data) < 16:
        raise ValueError("%s: shorter than a header" % what)
    table = int.from_bytes(data[8:16], "big")
    if table + 4 > len(data):
        raise ValueError("%s: the segment table is past the end" % what)
    count = int.from_bytes(data[table:table + 4], "big")
    off, segs = table + 4, {}
    for _ in range(count):
        if off + 4 > len(data):
            raise ValueError("%s: the segment table is cut short" % what)
        nlen = int.from_bytes(data[off:off + 4], "big")
        off += 4
        name = data[off:off + nlen].decode("utf-8", "replace")
        off += nlen
        pos = int.from_bytes(data[off:off + 8], "big")
        length = int.from_bytes(data[off + 8:off + 16], "big")
        digest = data[off + 16:off + 32]
        off += 32
        if pos + length > len(data):
            raise ValueError("%s: segment %s is past the end" % (what, name))
        if name in segs:
            raise ValueError("%s: segment %s named twice" % (what, name))
        segs[name] = (pos, length, digest)
    return segs


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


# ------------------------------------------------------------------ the checks


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
#: read).
EXEMPTIBLE_FIXTURES = ("place_same_file", "hint_removed", "channels_unchanged", "write_scheme_rewrite",
                       "vm_lia_hit")


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



class Fixture:
    def __init__(self, spec, rocq, out, segcmp):
        self.spec = spec
        self.rocq = rocq
        self.out = out
        self.segcmp = segcmp
        self.bad = []
        self.notes = []
        self.skip = None
        self.logs = out / "logs"
        self.logs.mkdir(parents=True, exist_ok=True)

    def fail(self, msg):
        self.bad.append(msg)

    def log(self, tag, res):
        (self.logs / (tag + ".json")).write_text(json.dumps(res, indent=1))

    # -- phases ------------------------------------------------------------
    def register(self, flags=None, reg_name="reg", records_name="records"):
        spec = self.spec
        flags = spec["register_flags"] if flags is None else flags
        reg = self.out / reg_name
        copy_tree(FIXTURES / spec["name"] / "original", reg)
        for src in spec["files"]:
            res = self.rocq.compile(spec, reg, flags + ["-proof-record"], src)
            self.log("%s-%s" % (reg_name, src), res)
            if res["rc"] != 0:
                self.fail("registration of %s exited %d: %s"
                          % (src, res["rc"], last_line(res)))
                return None
        records = self.out / records_name
        if records.exists():
            shutil.rmtree(records)
        records.mkdir(parents=True)
        published, err = publish_records(spec, reg, records)
        if err:
            self.fail(err)
            return None
        return records

    def check_records(self, reg_tree):
        """Parse every registration record, then apply fixture assertions."""
        for src in self.spec["files"]:
            path = record_src(reg_tree, src)
            try:
                _header, proofs, trailer = parse_record(path)
            except (ValueError, json.JSONDecodeError) as exc:
                self.fail("record of %s does not parse: %s" % (src, exc))
                continue
            # `record_trailers`: whether the record refers to its `.vo`.
            want_vo = self.spec.get("record_trailers", {}).get(src, {}).get("vo_opaques")
            if want_vo is not None and (trailer.get("vo_opaques") is not None) != want_vo:
                self.fail("record of %s: trailer vo_opaques is %r, wanted %s"
                          % (src, trailer.get("vo_opaques"), "a digest" if want_vo else "null"))
            by_name = {p.get("name"): p for p in proofs}
            wanted = self.spec["records"].get(src, {})
            for name, want in wanted.items():
                proof = by_name.get(name)
                if proof is None:
                    self.fail("record of %s has no entry for %s (it has %s)"
                              % (src, name, ", ".join(sorted(by_name)) or "none"))
                    continue
                reasons = [i.get("reason") for i in proof.get("ineligible", [])]
                for reason in want.get("ineligible", []):
                    if reason in reasons:
                        continue
                    if self.spec["trigger_optional"]:
                        # The fixture's own trigger did not fire on this Rocq.
                        # That is not a replay failure, and it must not pass
                        # silently either: the run prints it as a skip.
                        self.skip = ("%s: the registration did not mark it %r (it has %s); %s"
                                     % (name, reason, reasons or "no reason",
                                        self.spec["trigger_optional"]))
                        return
                    self.fail("%s: the registration did not mark it %r (it has %s)"
                              % (name, reason, reasons or "no reason"))
                if want.get("eligible") and reasons:
                    self.fail("%s: the registration marked it ineligible: %s" % (name, reasons))
                for field in want.get("writes_nonempty", []):
                    values = proof.get("writes", {}).get(field, [])
                    if not values:
                        self.fail("%s: the registration wrote no %s" % (name, field))
                if want.get("stores_no_term"):
                    if "replay" not in proof:
                        self.notes.append("%s: the record has no `replay` field "
                                          "(format v1: the recorder stores no term yet)" % name)
                    elif proof["replay"] is not None:
                        self.fail("%s: the registration stored a term for an ineligible proof" % name)
                # The stored blob's size: a record without the global universe
                # graph keeps a proof in a few kB, with it in tens.
                blob = proof.get("replay") or ""
                if "replay_max_bytes" in want and len(blob) > want["replay_max_bytes"]:
                    self.fail("%s: the stored term is %d bytes, wanted at most %d"
                              % (name, len(blob), want["replay_max_bytes"]))
                if "replay_min_bytes" in want and len(blob) < want["replay_min_bytes"]:
                    self.fail("%s: the stored term is %d bytes, wanted at least %d"
                              % (name, len(blob), want["replay_min_bytes"]))

    def grade(self, tree_name, flags, timeout_s=None, files=None):
        """Compile the edited tree in `tree_name`; stop at the first failure.

        `files` compiles a subset, in the given order: the mixed mode builds
        one object with replay and takes the rest from the stock tree.
        """
        spec = self.spec
        tree = self.out / tree_name
        copy_tree(FIXTURES / spec["name"] / "edited", tree)
        results = []
        for src in (spec["files"] if files is None else files):
            res = self.rocq.compile(spec, tree, flags, src, timeout_s=timeout_s)
            self.log("%s-%s" % (tree_name, src), res)
            results.append((src, res))
            if res["rc"] != 0:
                break
        return tree, results

    def replay_flags(self, records):
        """The replay compile's options: the fixture's own, where the record
        is, and the ratio.  With `replay_file`, the record is that file under
        `records`, given to `-proof-replay` with its SHA-256 (64 zeros when
        the file does not exist) as `-proof-replay-digest`.  Without it, the
        directory, to `-proof-replay-dir`."""
        spec = self.spec
        if spec["replay_file"] is None:
            source = ["-proof-replay-dir", str(records)]
        else:
            path = records / spec["replay_file"]
            digest = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else "0" * 64
            source = ["-proof-replay", str(path), "-proof-replay-digest", digest]
        return (spec["grade_flags"] + spec["replay_extra_flags"] + source
                + ["-proof-replay-ratio", spec["ratio"]])

    def check_exit_codes(self, replay, stock):
        spec = self.spec
        for src, res in replay:
            must_fail = src in spec["compile_fails"]
            if must_fail and res["rc"] == 0:
                self.fail("replay compiled %s, which must fail as stock does" % src)
            if not must_fail and res["rc"] != 0:
                self.fail("replay of %s exited %d: %s" % (src, res["rc"], last_line(res)))
        ra = [(s, r["rc"]) for s, r in replay]
        rb = [(s, r["rc"]) for s, r in stock]
        if ra != rb:
            self.fail("replay and stock disagree on exit codes: %s against %s" % (ra, rb))

    def check_summaries(self, tree, replay):
        spec = self.spec
        compiled = [src for src, res in replay if res["rc"] == 0]
        for src in spec["files"]:
            want = spec["summaries"].get(src)
            path = summary_src(tree, src)
            if want is None:
                if src in spec["compile_fails"] and path.exists():
                    self.fail("%s failed to compile but left a replay summary" % src)
                continue
            if not path.is_file():
                self.fail("no replay summary for %s" % src)
                continue
            if src not in compiled and src not in spec["compile_fails"]:
                self.fail("%s has a summary but did not compile" % src)
            try:
                got = json.loads(path.read_text())
            except json.JSONDecodeError as exc:
                self.fail("the replay summary of %s does not parse: %s" % (src, exc))
                continue
            self.compare_summary(src, want, got)

    def compare_summary(self, src, want, got):
        for field in ("proofs", "hits", "refused", "refused_detail", "killed", "fence"):
            if field in want and got.get(field) != want[field]:
                self.fail("%s: summary %s is %r, wanted %r" % (src, field, got.get(field), want[field]))
        if "misses" in want:
            misses = got.get("misses") or {}
            for kind in MISS_KINDS:
                if kind in want["misses"] and misses.get(kind) != want["misses"][kind]:
                    self.fail("%s: summary misses.%s is %r, wanted %r"
                              % (src, kind, misses.get(kind), want["misses"][kind]))
        if "outcomes" in want:
            if "outcomes" not in got:
                self.notes.append("%s: the summary has no `outcomes` field; "
                                  "only the counts were checked" % src)
            else:
                have = got["outcomes"]
                wanted = [list(x) for x in want["outcomes"]]
                basic = [[o.get("name"), o.get("outcome")] for o in have]
                wanted_basic = [x[:2] for x in wanted]
                if basic != wanted_basic:
                    self.fail("%s: outcomes are %s, wanted %s" % (src, basic, wanted_basic))
                for got_outcome, expected in zip(have, wanted):
                    if len(expected) >= 3 and got_outcome.get("channel") != expected[2]:
                        self.fail("%s: %s has mismatch channel %r, wanted %r"
                                  % (src, expected[0], got_outcome.get("channel"), expected[2]))
                    # [name, "read", channel, why]: why the read missed
                    # (no_evaluator, unknown, changed).
                    if len(expected) == 4 and got_outcome.get("why") != expected[3]:
                        self.fail("%s: %s missed for %r, wanted %r"
                                  % (src, expected[0], got_outcome.get("why"), expected[3]))

    def check_objects(self, a, b, replay):
        spec = self.spec
        both = []
        for src, res in replay:
            va, vb = vo_src(a, src), vo_src(b, src)
            if src in spec["compile_fails"]:
                for tree, path in (("replay", va), ("stock", vb)):
                    if path.exists():
                        self.fail("%s failed to compile but the %s run left %s" % (src, tree, path.name))
                continue
            if res["rc"] != 0:
                continue
            if not va.exists() or not vb.exists():
                self.fail("%s: a .vo is missing (replay %s, stock %s)"
                          % (src, va.exists(), vb.exists()))
                continue
            both.append(src)
        if not both:
            return []
        # The contract GRADE settled is BYTES: the engine's object store,
        # carry-over and registration key all match on the .vo digest, and a
        # sharing difference alone made a mixed tree refuse to load
        # (2026-10-25). The segment compare below normalises sharing, so a
        # raw cmp runs first and no fixture passes without it. The lane's own
        # compare went value-based in binary-equivalence-taiga #1403; this
        # suite does not follow it.
        for src in both:
            va, vb = vo_src(a, src), vo_src(b, src)
            if va.read_bytes() != vb.read_bytes():
                self.report_vo_diff(src, "bytes (the files are not identical)", trees=(a, b))
        if self.segcmp:
            listing = [src[:-2] + ".vo" for src in both]
            diffs, err = compare_trees_segcmp(self.segcmp, listing, a, b, self.out)
            if err:
                self.fail(err)
            else:
                for src in both:
                    key = src[:-2] + ".vo"
                    if key in diffs:
                        self.report_vo_diff(src, diffs[key], trees=(a, b))
            self.notes.append("objects compared by bytes, then with segcmp_norm --every-segment")
        else:
            for src in both:
                try:
                    bad = compare_vo_python(vo_src(a, src), vo_src(b, src))
                except ValueError as exc:
                    self.fail("%s: %s" % (src, exc))
                    continue
                if bad:
                    self.report_vo_diff(src, ",".join(bad), trees=(a, b))
            self.notes.append("objects compared by bytes, then in Python (segment bytes); "
                              "a vmlibrary-only difference cannot be decided here")
        return both

    def report_vo_diff(self, src, what, trees=None):
        """A `.vo` difference, and the one case a fixture may be excused.

        The conditions are in `exemption_allowed`; this gathers the facts it
        judges on. A missing object and a coqchk refusal are fatal on their
        own paths and never reach here.
        """
        if not self.spec["vo_exempt"].get(src) or trees is None:
            self.fail("%s: the replay .vo differs from stock in %s" % (src, what))
            return
        a, b = trees
        try:
            differing = compare_vo_python(vo_src(a, src), vo_src(b, src))
        except ValueError as exc:
            self.fail("%s: %s" % (src, exc))
            return
        allowed, why = exemption_allowed(self.spec["name"], differing, self.library_values_equal(a, b, src))
        if allowed:
            self.notes.append("%s: .vo differs (%s), exempt: %s [%s]"
                              % (src, what, self.spec["vo_exempt"][src], why))
        else:
            self.fail("%s: the replay .vo differs from stock and is NOT excusable: %s" % (src, why))

    def library_values_equal(self, a, b, src):
        """Does the library segment hold the same VALUE on both sides?

        Only `vodiff.py` can tell a value difference from a sharing one: it
        decodes the Marshal stream and resolves its shared pointers.
        """
        tool = pathlib.Path(__file__).resolve().parent / "vodiff.py"
        p = subprocess.run([sys.executable, str(tool), str(vo_src(a, src)), str(vo_src(b, src)), "library"],
                           capture_output=True, text=True)
        lines = [l for l in p.stdout.splitlines() if "value differences" in l]
        return bool(lines) and lines[-1].startswith("0 value differences")


    def check_coqchk(self, tree, compiled):
        if not self.spec["coqchk"] or not compiled:
            return
        libs = [lib_name(self.spec, src) for src in compiled]
        res = self.rocq.coqchk(self.spec, tree, libs)
        self.log("coqchk", res)
        if res["rc"] != 0:
            self.fail("coqchk rejected the replay objects (exit %d): %s" % (res["rc"], last_line(res)))

    def check_output(self, replay, stock):
        spec = self.spec
        ra = {src: res for src, res in replay}
        rb = {src: res for src, res in stock}
        for src in spec["compare_stdout"]:
            if src in ra and src in rb and ra[src]["out"] != rb[src]["out"]:
                self.fail("%s: replay and stock print different stdout%s" % (src, first_diff(ra[src]["out"], rb[src]["out"])))
        for src in spec["compare_stderr"]:
            if src in ra and src in rb and ra[src]["err"] != rb[src]["err"]:
                self.fail("%s: replay and stock print different stderr%s" % (src, first_diff(ra[src]["err"], rb[src]["err"])))
        for src, needles in spec["stdout_contains"].items():
            for needle in needles:
                if src in ra and needle not in ra[src]["out"]:
                    self.fail("%s: the replay run did not print %r on stdout" % (src, needle))
        for src, needles in spec["stderr_contains"].items():
            for needle in needles:
                if src in ra and needle not in ra[src]["err"]:
                    self.fail("%s: the replay run did not print %r on stderr" % (src, needle))

    # -- modes -------------------------------------------------------------
    def run_replay_mode(self, records, stock_control=False):
        spec = self.spec
        if stock_control:
            # No replay option on either side: this exercises the runner's own
            # halves (exit codes, the object comparison, coqchk, the output
            # comparison) and states the box's stock-against-stock noise,
            # before a replay Rocq exists.
            replay_flags = spec["grade_flags"]
        else:
            replay_flags = self.replay_flags(records)
        a, replay = self.grade("a", replay_flags)
        b, stock = self.grade("b", spec["grade_flags"])
        self.check_exit_codes(replay, stock)
        if not stock_control:
            self.check_summaries(a, replay)
        compiled = self.check_objects(a, b, replay)
        self.check_coqchk(a, compiled)
        self.check_output(replay, stock)
        if not stock_control and spec.get("alt_register_flags") is not None:
            self.compare_alt_format(a, replay)

    def compare_alt_format(self, a, replay):
        """`alt_register_flags`: register the same tree again with those flags
        (another record format), replay the edited tree from that record in
        `c/`, and require the same exit codes, the same hits and the same
        `.vo` bytes as the replay from the first record: the two formats
        replay to one outcome."""
        spec = self.spec
        records = self.register(flags=spec["alt_register_flags"], reg_name="rgb", records_name="recordz")
        if records is None:
            return
        flags = self.replay_flags(records)
        c, other = self.grade("c", flags)
        ra = [(s, r["rc"]) for s, r in replay]
        rc = [(s, r["rc"]) for s, r in other]
        if ra != rc:
            self.fail("the two record formats disagree on exit codes: %s against %s" % (ra, rc))
            return
        for src, res in replay:
            if res["rc"] != 0:
                continue
            ha = json.loads(summary_src(a, src).read_text()).get("hits")
            hc = json.loads(summary_src(c, src).read_text()).get("hits")
            if ha != hc:
                self.fail("%s: %r hits from the first record, %r from the other format" % (src, ha, hc))
            if vo_src(a, src).read_bytes() != vo_src(c, src).read_bytes():
                self.fail("%s: the .vo replayed from the two record formats differ" % src)
        self.notes.append("the record format %s replays to the same .vo bytes"
                          % (" ".join(spec["alt_register_flags"]) or "with no format flag"))

    def run_usage_mode(self, records):
        """`-proof-replay` with no ratio: a usage error before any compile."""
        spec = self.spec
        src = spec["files"][0]
        record = records / (lib_name(spec, src) + ".proof-record.jsonl")
        if not record.is_file():
            record = records / (lib_name(spec, src).replace(".", "/") + ".proof-record.jsonl")
        tree = self.out / "u"
        copy_tree(FIXTURES / spec["name"] / "edited", tree)
        res = self.rocq.compile(spec, tree, ["-proof-replay", str(record)], src)
        self.log("usage-" + src, res)
        want_rc = spec["usage"].get("exit", 1)
        if res["rc"] != want_rc:
            self.fail("`-proof-replay` with no ratio exited %d, wanted %d: %s"
                      % (res["rc"], want_rc, last_line(res)))
        text = res["out"] + res["err"]
        for needle in spec["usage"].get("message_contains", []):
            if needle.lower() not in text.lower():
                self.fail("the error does not name %r: %s" % (needle, text.strip()[:300]))
        if vo_src(tree, src).exists():
            self.fail("the refused compile still wrote %s" % vo_src(tree, src).name)

    def run_budget_mode(self, records):
        spec = self.spec
        budget = spec["budget"]
        src = spec["files"][0]
        replay_flags = self.replay_flags(records) + ["-proof-replay-budget", str(budget)]
        a, replay = self.grade("a", replay_flags, timeout_s=budget + 120)
        b, stock = self.grade("b", spec["grade_flags"], timeout_s=budget)
        ra, rb = replay[0][1], stock[0][1]
        if ra["rc"] != 124:
            self.fail("the replay compile exited %d, wanted 124 (a charged kill): %s"
                      % (ra["rc"], last_line(ra)))
        if rb["rc"] != 124:
            self.fail("the stock compile exited %d, wanted 124 (its own timeout): %s"
                      % (rb["rc"], last_line(rb)))
        limit = spec["replay_wall_max"] or (budget - 20)
        if ra["rc"] == 124 and ra["wall"] >= limit:
            self.fail("the replay compile ran %.1fs, so the wrapper killed it, not the charged clock"
                      % ra["wall"])
        self.notes.append("replay wall %.1fs, stock wall %.1fs, budget %ds" % (ra["wall"], rb["wall"], budget))
        for tree, label in ((a, "replay"), (b, "stock")):
            if vo_src(tree, src).exists():
                self.fail("the killed %s compile still wrote %s" % (label, vo_src(tree, src).name))
        want = spec["summaries"].get(src)
        if want is not None:
            path = summary_src(a, src)
            if not path.is_file():
                self.fail("the killed replay compile wrote no summary")
            else:
                self.compare_summary(src, want, json.loads(path.read_text()))

    def run_mixed_mode(self, records):
        """The carry-over case: one object is REUSED, its dependency REPLAYED.

        A `.vo` records a digest of each library it was compiled against, so a
        reused object only loads beside a replayed dependency if the replayed
        object is the same bytes stock would have written.  The fixture
        therefore builds three trees: `b` holds a stock object for every file
        and is the control, `a` holds the replayed object of one file, and `m`
        holds the replayed object beside the stock objects of the files that
        were compiled against the stock one.  The files named in
        `mixed.check_files` are then compiled in `m`, and must do what they do
        in the control.  Without the control a broken setup would look like a
        pass, so the control's own failure ends the fixture.
        """
        spec = self.spec
        cfg = spec["mixed"]
        replay_file = cfg["replay_file"]
        carry = cfg["carry_files"]
        check = cfg["check_files"]
        b, stock = self.grade("b", spec["grade_flags"])
        for src, res in stock:
            if res["rc"] != 0:
                self.fail("the stock control failed to compile %s (exit %d), so the mixed tree proves nothing: %s"
                          % (src, res["rc"], last_line(res)))
                return
        for src, needles in spec["stdout_contains"].items():
            got = dict(stock).get(src)
            for needle in needles:
                if got is not None and needle not in got["out"]:
                    self.fail("the stock control of %s did not print %r, so the mixed tree proves nothing"
                              % (src, needle))
                    return
        replay_flags = self.replay_flags(records)
        a, replay = self.grade("a", replay_flags, files=[replay_file])
        if replay[0][1]["rc"] != 0:
            self.fail("the replay compile of %s exited %d: %s"
                      % (replay_file, replay[0][1]["rc"], last_line(replay[0][1])))
            return
        self.check_summaries(a, replay)
        m = self.out / "m"
        copy_tree(FIXTURES / spec["name"] / "edited", m)
        shutil.copyfile(vo_src(a, replay_file), vo_src(m, replay_file))
        for src in carry:
            shutil.copyfile(vo_src(b, src), vo_src(m, src))
        self.notes.append("mixed tree: %s replayed, %s reused from the stock build"
                          % (replay_file, ", ".join(carry)))
        mixed = []
        for src in check:
            res = self.rocq.compile(spec, m, spec["grade_flags"], src)
            self.log("m-" + src, res)
            mixed.append((src, res))
            if res["rc"] != 0:
                self.fail("the mixed tree failed to compile %s (exit %d): %s"
                          % (src, res["rc"], last_line(res)))
        self.check_output(mixed, stock)
        self.check_coqchk(m, carry)

    def run(self, register_only=False, stock_control=False):
        records = self.register()
        if records is None:
            return
        self.check_records(self.out / "reg")
        if register_only or self.skip:
            return
        if stock_control:
            if self.spec["mode"] != "replay":
                self.skip = "stock control covers replay-mode fixtures only"
                return
            self.notes.append("stock control: no replay option on either side")
            self.run_replay_mode(records, stock_control=True)
            return
        if self.spec["mode"] == "usage":
            self.run_usage_mode(records)
        elif self.spec["mode"] == "budget":
            self.run_budget_mode(records)
        elif self.spec["mode"] == "mixed":
            self.run_mixed_mode(records)
        else:
            self.run_replay_mode(records)


def last_line(res):
    text = (res["err"] or res["out"]).strip().splitlines()
    return text[-1][:300] if text else "(no output)"


def first_diff(a, b):
    la, lb = a.splitlines(), b.splitlines()
    for i in range(max(len(la), len(lb))):
        x = la[i] if i < len(la) else "(end)"
        y = lb[i] if i < len(lb) else "(end)"
        if x != y:
            return "; first difference at line %d: replay %r, stock %r" % (i + 1, x[:160], y[:160])
    return ""


# ------------------------------------------------------------- prerequisites


def probe(rocq, spec, out, what):
    """Is a prerequisite of a fixture there?  Returns None, or why not."""
    if what == "csdp":
        return None if shutil.which("csdp") else "no csdp in PATH"
    if what == "native":
        work = out / "probe-native"
        work.mkdir(parents=True, exist_ok=True)
        src = "NativeProbe.v"
        (work / src).write_text("Lemma probe : 2 + 2 = 4.\nProof. native_compute. reflexivity. Qed.\n")
        res = rocq.run([str(rocq.bin / "rocq"), "compile", "-q", "-native-compiler", "ondemand",
                        "-Q", ".", "Probe", src], work)
        if res["rc"] != 0:
            return "native_compute does not run here: " + last_line(res)
        return None
    return "unknown prerequisite %r" % what


# -------------------------------------------------------------------- driving


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
            spec = load_spec(name)
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
        spec = load_spec(name)
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
            shutil.rmtree(work)
        work.mkdir(parents=True)
        fix = Fixture(spec, rocq, work, segcmp)
        try:
            fix.run(register_only=args.register_only, stock_control=args.stock_control)
        except Exception as exc:  # a broken fixture is a failure, not a crash
            fix.fail("the runner raised %s: %s" % (type(exc).__name__, exc))
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
