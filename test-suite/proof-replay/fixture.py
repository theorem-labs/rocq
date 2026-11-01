"""One fixture, run (BET-84).

One fixture is a tiny Rocq project in two versions, `original/` and
`edited/`, plus `expect.json`.  For one fixture the runner does, in order:

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
    compiled, the same `.vo` (vo_compare.py).
5.  **coqchk.**  `rocqchk` over the replay run's objects must accept them.

`a/` and `b/` are one character each because an object's `vmlibrary` bytes
depend on the length of the build path.
"""

import hashlib
import json
import math
import shutil

from records import parse_record, publish_records
from rocq import last_line
from trees import lib_name, record_src, remove_tree, stage_tree, summary_src, vo_src
from vo_compare import compare_trees_segcmp, compare_vo_python, exemption_allowed, library_values_equal

MISS_KINDS = ("key", "read", "ineligible", "missing_record")

#: Budget mode: how far into the last proof's recorded wall time the budget
#: ends.  The stock compile must still outlast the budget, and it runs every
#: proof at about the recorded speed less the recorder's overhead: 0.3 leaves
#: about a quarter of a proof between them.
BUDGET_LAST_SHARE = 0.3


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
        stage_tree(spec, "original", reg)
        for src in spec["files"]:
            res = self.rocq.compile(spec, reg, flags + ["-proof-record"], src)
            self.log("%s-%s" % (reg_name, src), res)
            if res["rc"] != 0:
                self.fail("registration of %s exited %d: %s"
                          % (src, res["rc"], last_line(res)))
                return None
        records = self.out / records_name
        if records.exists():
            remove_tree(records)
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
        stage_tree(spec, "edited", tree)
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
        # compare went value-based in the grading harness on 2026-10-25; this
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
        allowed, why = exemption_allowed(self.spec["name"], differing,
                                         library_values_equal(vo_src(a, src), vo_src(b, src)))
        if allowed:
            self.notes.append("%s: .vo differs (%s), exempt: %s [%s]"
                              % (src, what, self.spec["vo_exempt"][src], why))
        else:
            self.fail("%s: the replay .vo differs from stock and is NOT excusable: %s" % (src, why))

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
        stage_tree(spec, "edited", tree)
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
        """The charged clock kills the replay compile inside the last proof.

        The budget comes from this machine's registration, so the fixture
        holds on a slow box as on a fast one: the recorded wall times of the
        proofs before the last are the charge of the hits, and the budget ends
        BUDGET_LAST_SHARE of the way into the last proof's recorded time.  The
        stock compile, which runs every proof, must outlast that budget.  A
        kill that lands only after the last proof's tactic finishes takes at
        least the whole proof, so the replay wall must stay under twice the
        share.
        """
        spec = self.spec
        src = spec["files"][0]
        try:
            _, proofs, _ = parse_record(record_src(self.out / "reg", src))
        except ValueError as exc:
            self.fail("cannot read the registration's record of %s: %s" % (src, exc))
            return
        walls = [p["wall_s"] for p in proofs]
        if len(walls) < 2:
            self.fail("the budget needs at least two recorded proofs, %s has %d" % (src, len(walls)))
            return
        charge = sum(walls[:-1])
        budget = int(math.ceil(charge + BUDGET_LAST_SHARE * walls[-1]))
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
        limit = 2 * (budget - charge)
        if ra["rc"] == 124 and ra["wall"] >= limit:
            self.fail("the replay compile ran %.1fs (limit %.1fs), so the kill did not land inside the last "
                      "proof's tactic" % (ra["wall"], limit))
        self.notes.append("recorded proofs %s s, charge %.1fs, budget %ds, replay wall %.1fs, stock wall %.1fs"
                          % ("/".join("%.1f" % w for w in walls), charge, budget, ra["wall"], rb["wall"]))
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
        stage_tree(spec, "edited", m)
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
        # A Rocq configured without native code only warns and falls back to
        # vm_compute, so the probe makes that warning an error.
        res = rocq.run([str(rocq.bin / "rocq"), "compile", "-q", "-native-compiler", "ondemand",
                        "-w", "+native-compiler-disabled", "-Q", ".", "Probe", src], work)
        if res["rc"] != 0:
            return "native_compute does not run here: " + last_line(res)
        return None
    return "unknown prerequisite %r" % what
