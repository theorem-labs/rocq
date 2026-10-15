#!/usr/bin/env python3
"""Drop-in replacement for the `rocq` binary coq_makefile's generated Makefile
invokes as `$(ROCQ) compile <flags...> <file.v>` (ROCQ ?= "$(COQBIN)rocq").

The usage-cutoff fork's loader already accepts a dependent .vo whose own
source is unchanged, against a rebuilt dependency, whenever the per-declaration
interface subset it recorded still matches (Admitted->Qed, an unused addition).
coq_makefile's generated rules only ever check *mtimes*: a target is rebuilt
whenever any of its direct-dependency .vo files is newer, with no reference to
whether the fork would actually refuse it. This wrapper closes that gap:

  0. Structural eligibility (binary-equivalence-taiga#841 D5, findings 2/M2,
     Major-5, m4; hardened per BugFinderRedTeamV2 M4): only `compile` invoked
     with EXACTLY a known-safe flag set (-Q/-R/-I/-noinit/-q/-w/...) followed
     by one trailing .v file is eligible for the cutoff at all. `-vos`,
     `-vok`, `-vio`, `-beautify` -- and any other flag this driver doesn't
     recognize, including a future Rocq flag in the same family -- `execv`
     straight to REAL_ROCQ with NO stamp read or write of any kind, before
     any cutoff logic runs. v1's dispatch only checked `argv[0] != "compile"`,
     which does not catch these: they are flags inside `compile`'s own argv,
     not a different subcommand, so `make vos` would stamp a source as
     "rebuilt" without ever having produced a .vo, and a later `make`
     (building the real .vo) would wrongly reuse the stale one.
  1. Own-source check (never skipped): compare the sha256 of the .v file
     being "compiled", HASHED ONCE BEFORE the real compiler ever runs, against
     the hash recorded the last time this wrapper actually ran a real compile
     (a `<file>.vo.cutoff-stamp` sidecar, JSON since #841 Review841 G3/G4 --
     see below). Missing stamp, missing .vo, or a hash mismatch -> always a
     real compile. (v1 hashed AFTER `subprocess.run` returned and wrote that
     re-derived value -- a TOCTOU: an edit landing during the compile got
     recorded against the OLD .vo. Fixed by capturing `pre_hash` exactly once
     and never re-deriving it.)

     The own-source hash alone only covers the `.v` file's own bytes. Two
     gaps Review841 reproduced on top of it (issue #841 issuecomment-
     6187211433, findings G3/G4) are closed the same way, both gated behind
     the matching own-source hash so none of this runs on a changed `.v`:

       - G3 (`Load`/`Extra Dependency`/plugin prerequisites are invisible to
         the stamp): `rocq dep` already classifies every such prerequisite
         for this exact file (`tools/coqdep/lib/common.ml`'s `Require`/
         `Declare`/`Load`/`External` cases, rendered as a Make dependency
         line by `tools/coqdep/lib/makefile.ml`'s `print_dep`). Every real
         build runs `rocq dep` itself for this one file (no reliance on
         locating coq_makefile's project-wide `.d` file, whose name depends
         on the Makefile's own `-o` name and isn't recoverable from this
         driver's argv), hashes every prerequisite coqdep lists EXCEPT the
         `.vo`/`.vos`/`.vok`/`.glob` artifacts of other libraries (those are
         already covered by make's own mtime cascade plus their own
         per-file stamp), and records the set in the stamp. A REUSE decision
         re-hashes every one of those files and refuses unless all of them
         still match.
       - G4 (the stamp isn't bound to the `.vo` it describes): hand-editing
         the `.v` and reverting it, or hand-editing the `.vo` directly
         (bypassing this driver, e.g. running `rocq c` by hand), can leave a
         stamp whose `v_hash` still matches the reverted `.v` while the
         `.vo` on disk reflects something this driver never produced. Every
         real build also records the sha256 of the `.vo` it just produced,
         read AFTER the compile (a different value from `v_hash`, which must
         stay captured BEFORE compiling per the TOCTOU fix above -- the two
         protect different things and must never be conflated). A REUSE
         decision re-hashes the CURRENT `.vo` and refuses unless it still
         matches.
  2. Interactive gate: the cutoff (reuse) logic below is only reachable when
     `CUTOFF_AGENT_INTERACTIVE=1` is set in the environment; otherwise this
     driver always real-builds, unconditionally, even against a matching
     stamp. v1 had this inverted (`BET_GRADING`, an opt-OUT nothing ever set,
     so the guard was inert by construction); this fails closed for any
     caller that doesn't explicitly opt in instead.
  3. Cheap acceptance check (only reached when the own source, the recorded
     `.vo`, and every recorded dependency's content all still match, i.e.
     make invoked us only because some dependency's .vo got a newer mtime):
     derive this file's logical (dotted) module name from the -Q/-R
     bindings in the same argv coq_makefile already built, and ask a
     throwaway `coqtop -batch ... -require <logical>` whether the existing
     .vo is still loadable. This is exactly Rocq's own Require-time
     consistency check (vernac/library.ml's file-level gate +
     kernel/safe_typing.ml's check_required) with none of the proof
     elaboration a real compile would redo -- cheap by construction, not by
     sampling.
  4. If step 3 accepts: freshen (never rewrite the bytes of) every target
     this driver's compile recipe normally produces -- the .vo and .glob from
     CoqMakefile.in's grouped `$(1).vo $(1).glob &: $(1).v` rule -- so a
     SUBSEQUENT `make` invocation sees this target as up to date and never
     re-invokes this driver (and therefore never re-runs the `coqtop
     -require` check) for the identical state, and so anything that in turn
     depends on this file is never even visited by coq_makefile's own mtime
     check. v1 returned on REUSED without updating any state, so `make -q`
     never settled and every later `make` re-ran the same cheap check. The
     new mtime is bounded "restat" semantics (#841 Review841 G5, see
     `touch_reused_targets`), not an unconditional forward push.
  5. If step 3 refuses (or anything about it is inconclusive: a nested
     module/functor the fork's interface table can't represent, the
     subprocess failing to start, etc.): fall back to a real compile. This is
     the fail-safe direction -- never skip when unsure, only ever skip when a
     cheap, explicit check proved the fork would already have proved reuse
     safe.

Every result this driver reuses is one the fork's own loader and, at grade
time, coqchk, independently re-verify (CARRY-BUILD-PROTO.md's "coqchk is the
trust anchor" and this fork's own Require-time gate: see ROCQ-USAGE-CUTOFF.md
S4). This driver changes nothing about what gets *proof-checked* -- only what
gets *recompiled*. It is also never wired into BET's grading toolchain at all
(binary-equivalence-taiga#841, "Deployment scope"): the one real caller is the
agent's own interactive `rocq_write`/`rocq_restart` MCP session loop, which is
exactly the caller `CUTOFF_AGENT_INTERACTIVE=1` names.
"""
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path

REAL_ROCQ = os.environ.get(
    "CUTOFF_REAL_ROCQ", "/rocq/rocq-usage-cutoff/_build/install/default/bin/rocq"
)
COQTOP = os.environ.get(
    "CUTOFF_COQTOP", os.path.join(os.path.dirname(REAL_ROCQ), "coqtop")
)
STATS_LOG = os.environ.get("CUTOFF_STATS_LOG")
# Default BLOCKED (#841 D5, BugFinderRedTeamV2 M3): the cutoff is only ever
# attempted when the one real caller explicitly opts in. Any other caller --
# known today or added later -- gets the always-correct, always-real-build
# behavior with no separate opt-out to wire up.
AGENT_INTERACTIVE = os.environ.get("CUTOFF_AGENT_INTERACTIVE") == "1"

# Flags coq_makefile's generated recipes are known to pass to `rocq compile`
# that do not change its .vo-producing behavior, mapped to the number of
# argv tokens each one consumes AFTER itself (its arity). Anything not in
# this table -- a flag coq_makefile doesn't emit today, or one of the
# non-.vo-producing flags below -- makes the whole invocation cutoff-
# ineligible; see `classify_compile`.
SAFE_FLAG_ARITY = {
    "-q": 0,
    "-noinit": 0,
    "-Q": 2,
    "-R": 2,
    "-I": 1,
    "-w": 1,
    "-native-compiler": 1,
    "-deprecated-native-compiler-option": 0,
    "-time-file": 1,
    "-profile": 1,
}

# `compile` flags that put the compiler into a mode that does not produce (or
# does not fully rewrite) a `.vo`: -vos/-vok/-vio produce lighter-weight
# artifacts instead, -beautify only reformats the source. Named here only as
# a fast, explicit check matching #841 D5's wording directly -- the general
# structural parse in `classify_compile` already rejects all of these (and
# any FUTURE flag in the same family) by virtue of not appearing in
# SAFE_FLAG_ARITY, per BugFinderRedTeamV2 M4: prefer a structural test over
# enumeration, fail toward more bypassing never toward more reuse.
NON_VO_FLAGS = frozenset({"-vos", "-vok", "-vio", "-beautify"})

# `compile`-only flags inside SAFE_FLAG_ARITY that `rocq dep`'s own argv
# parser (`tools/coqdep/lib/args.ml`) either doesn't recognize or would
# misparse (an unrecognized flag taking an argument has that argument
# swallowed as a bare positional file, since coqdep's unknown-option
# fallthrough doesn't know the dropped flag's arity): `-native-compiler`,
# `-time-file`, `-profile` all take an argument and are irrelevant to
# dependency computation; `-w`/`-q`/`-noinit`/
# `-deprecated-native-compiler-option` are 0-arity so harmless either way but
# equally irrelevant. Only `-Q`/`-R`/`-I` establish the loadpath `rocq dep`
# needs to resolve `Require`/`Load` the same way `rocq compile` itself will.
DEP_FLAG_ARITY = {"-Q": 2, "-R": 2, "-I": 1}

# Prerequisite extensions that name another library's own build artifact
# (produced by a `Require`d `.v` file's own compile). Content changes there
# are already covered by make's own mtime cascade plus that file's own
# per-file stamp chain; #841 Review841 G3 is about prerequisites those
# checks never see at all (`Load`, `Extra Dependency`, `Declare ML Module`
# plugin files), so they are excluded from the G3 content-hash set.
ARTIFACT_EXTS = (".vo", ".vos", ".vok", ".glob")


def log(kind: str, vfile: str, extra: str = "") -> None:
    if STATS_LOG:
        with open(STATS_LOG, "a") as f:
            f.write(f"{kind}\t{vfile}\t{extra}\n")


def sha256_of(path: str) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def classify_compile(rest: list[str]) -> tuple[list[str], str] | None:
    """Parse the argv following `compile`. Returns `(flags, vfile)` iff
    `rest` is EXACTLY a sequence of `SAFE_FLAG_ARITY`-recognized flags
    followed by one trailing `.v` file -- the only shape the cutoff logic
    below is sound for. Anything else -- an unrecognized flag, one of
    `NON_VO_FLAGS`, no trailing `.v`, a flag's arity running past or short of
    the final token -- returns `None`, which the caller must treat as
    cutoff-ineligible and forward to `REAL_ROCQ` untouched with no stamp
    interaction at all.
    """
    if not rest:
        return None
    if any(tok in NON_VO_FLAGS for tok in rest):
        return None
    i = 0
    flags: list[str] = []
    while i < len(rest) - 1:
        arity = SAFE_FLAG_ARITY.get(rest[i])
        if arity is None:
            return None
        consumed = rest[i : i + 1 + arity]
        if len(consumed) != 1 + arity:
            return None
        flags.extend(consumed)
        i += 1 + arity
    if i != len(rest) - 1:
        return None
    vfile = rest[-1]
    if vfile.startswith("-") or not vfile.endswith(".v"):
        return None
    return flags, vfile


def derive_logical_name(vfile: str, loadpath: list[tuple[str, str, str]]) -> str | None:
    """loadpath: list of (kind, physdir, logical) from -Q/-R flags, in argv
    order. Not flagged as broken by #841 D5 (only symlink/case-insensitivity
    edge cases in path comparison are noted as Minor, left unfixed here).
    """
    vabs = os.path.normpath(vfile)
    best = None  # (len(physdir_norm), logical, physdir_norm)
    for _kind, physdir, logical in loadpath:
        pd = os.path.normpath(physdir)
        rel = os.path.relpath(vabs, pd)
        if rel.startswith(".."):
            continue
        if best is None or len(pd) > best[0]:
            best = (len(pd), logical, pd)
    if best is None:
        return None
    _len, logical, pd = best
    rel = os.path.relpath(vabs, pd)
    if not rel.endswith(".v"):
        return None
    parts = rel[: -len(".v")].split(os.sep)
    if logical:
        parts = [logical] + parts
    return ".".join(parts)


def parse_loadpath(flags: list[str]) -> list[tuple[str, str, str]]:
    out = []
    i = 0
    while i < len(flags):
        if flags[i] in ("-Q", "-R") and i + 2 < len(flags):
            out.append((flags[i], flags[i + 1], flags[i + 2]))
            i += 3
        else:
            i += 1
    return out


def extract_dep_flags(flags: list[str]) -> list[str]:
    """The subset of an already-classified `compile` flag list worth
    forwarding to `rocq dep` (#841 Review841 G3): only `-Q`/`-R`/`-I`,
    which establish the same loadpath bindings `rocq compile` itself uses to
    resolve `Require`/`Load`. Everything else in `SAFE_FLAG_ARITY` is either
    irrelevant to dependency computation or actively unsafe to forward (see
    `DEP_FLAG_ARITY`'s comment).
    """
    out: list[str] = []
    i = 0
    while i < len(flags):
        arity = DEP_FLAG_ARITY.get(flags[i])
        if arity is not None and i + arity < len(flags):
            out.extend(flags[i : i + 1 + arity])
            i += 1 + arity
        else:
            i += 1
    return out


def _split_make_tokens(rhs: str) -> list[str]:
    """Split the right-hand side of a Make dependency rule into its
    individual prerequisite tokens, honoring `tools/coqdep/lib/makefile.ml`
    `escape`'s rules: a backslash makes the following character literal
    (including a literal space, so it is not a token separator), and `$$`
    unescapes to a single `$`.
    """
    tokens: list[str] = []
    cur: list[str] = []
    i = 0
    while i < len(rhs):
        c = rhs[i]
        if c == "\\" and i + 1 < len(rhs):
            cur.append(rhs[i + 1])
            i += 2
            continue
        if c.isspace():
            if cur:
                tokens.append("".join(cur).replace("$$", "$"))
                cur = []
            i += 1
            continue
        cur.append(c)
        i += 1
    if cur:
        tokens.append("".join(cur).replace("$$", "$"))
    return tokens


def parse_coqdep_deps(output: str) -> list[str]:
    """Parse the first Make-rule line of `rocq dep`'s stdout for a single
    `.v` file -- exactly the format `tools/coqdep/lib/makefile.ml`'s
    `print_dep` emits (`name.vo name.glob name.v.beautified
    name.required_vo: name.v dep1 dep2 ...`) -- and return the full
    right-hand-side token list, in order: the file's own `.v`, every
    `Require`d library as a `.vo` path, every `Declare ML Module` plugin as
    a `.cma`/`.cmxs` path, every `Load`ed/`Extra Dependency` file and the
    worker path as raw paths (`tools/coqdep/lib/common.ml`'s `Require`/
    `Declare`/`Load`/`External` classification). The left-hand side ends at
    the first unescaped `:`, found the same way coqdep's own escaping makes
    it unambiguous. Returns `[]` if no parseable rule line is found.
    """
    for line in output.splitlines():
        if not line.strip():
            continue
        i = 0
        colon = None
        while i < len(line):
            if line[i] == "\\" and i + 1 < len(line):
                i += 2
                continue
            if line[i] == ":":
                colon = i
                break
            i += 1
        if colon is None:
            continue
        return _split_make_tokens(line[colon + 1 :])
    return []


def compute_prereqs(flags: list[str], vfile: str) -> list[str] | None:
    """Run `rocq dep` for exactly this one `.v` file (never relying on
    locating coq_makefile's own project-wide dependency file, whose name
    depends on the Makefile's `-o` name, which isn't recoverable from this
    driver's argv) and return coqdep's full prerequisite list for it.
    Returns `None` if `rocq dep` can't be run, exits nonzero, or its output
    doesn't parse -- callers must treat that as "can't confirm", the same
    fail-toward-rebuild direction as every other check here.
    """
    cmd = [REAL_ROCQ, "dep"] + extract_dep_flags(flags) + [vfile]
    try:
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    except OSError:
        return None
    if r.returncode != 0:
        return None
    tokens = parse_coqdep_deps(r.stdout.decode("utf-8", "replace"))
    return tokens or None


def dep_hashes_match(dep_hashes: dict[str, str]) -> bool:
    """#841 Review841 G3: re-hash every prerequisite recorded in the stamp
    and require ALL of them to still match -- a missing file counts as a
    mismatch, never as "nothing to check".
    """
    for path, expected in dep_hashes.items():
        try:
            if sha256_of(path) != expected:
                return False
        except OSError:
            return False
    return True


def read_stamp(stamp: str) -> dict | None:
    try:
        data = json.loads(Path(stamp).read_text())
    except (OSError, ValueError):
        return None
    if not isinstance(data, dict) or "v_hash" not in data:
        return None
    return data


def write_stamp(
    stamp: str,
    v_hash: str,
    vo_hash: str | None,
    dep_hashes: dict[str, str] | None,
    prereqs: list[str] | None,
) -> None:
    Path(stamp).write_text(
        json.dumps(
            {"v_hash": v_hash, "vo_hash": vo_hash, "dep_hashes": dep_hashes, "prereqs": prereqs},
            sort_keys=True,
        )
    )


def real_build(flags: list[str], vfile: str, vo: str, stamp: str, pre_hash: str) -> None:
    """Run the real compiler. `pre_hash` MUST be the sha256 of `vfile`
    captured before this call, and is written to the stamp verbatim, never
    re-derived -- #841 D5 / BugFinderRedTeamV2 M1: hashing again after
    `subprocess.run` returns can record a hash that doesn't match what was
    actually fed to the compiler, if `vfile` changed mid-compile.

    On success, also records (#841 Review841 G3/G4) the sha256 of the
    resulting `.vo` -- read AFTER the compile, since that is genuinely the
    file whose identity the next REUSE decision must bind to, a different
    value from `pre_hash` which protects a different thing and must stay
    captured before compiling -- and the sha256 of every non-artifact
    prerequisite `rocq dep` lists for this file OTHER than `vfile` itself
    (already covered, pre-compile, by `pre_hash`/`v_hash` -- hashing it
    again here would both be redundant and reintroduce exactly the
    post-compile TOCTOU read M1 eliminated, just for a second field), plus
    the raw prerequisite list itself (including `vfile`) for
    `touch_reused_targets`'s bounded restat (G5). Any failure computing
    those (the `rocq dep` subprocess failing, a listed prerequisite missing
    from disk) records `None` rather than a partial or stale value, so a
    later REUSE decision that can't confirm them fails closed into a real
    rebuild instead of silently skipping the check.
    """
    cmd = [REAL_ROCQ, "compile"] + flags + [vfile]
    r = subprocess.run(cmd)
    if r.returncode == 0:
        try:
            vo_hash = sha256_of(vo)
        except OSError:
            vo_hash = None
        prereqs = compute_prereqs(flags, vfile)
        dep_hashes: dict[str, str] | None
        if prereqs is None:
            dep_hashes = None
        else:
            dep_hashes = {}
            for tok in prereqs:
                if tok.endswith(ARTIFACT_EXTS) or os.path.normpath(tok) == os.path.normpath(vfile):
                    continue
                try:
                    dep_hashes[tok] = sha256_of(tok)
                except OSError:
                    dep_hashes = None
                    break
        write_stamp(stamp, pre_hash, vo_hash, dep_hashes, prereqs)
        log("REBUILD", vfile)
    else:
        log("FAIL", vfile, str(r.returncode))
    sys.exit(r.returncode)


def touch_reused_targets(vo: str, glob: str, prereqs: list[str]) -> None:
    """After a REUSED verdict, freshen every target CoqMakefile.in's grouped
    `$(1).vo $(1).glob &: $(1).v` rule normally produces, WITHOUT rewriting
    their bytes, so a subsequent `make` (a) considers this target up to date
    and never re-invokes this driver (never re-runs the `coqtop -require`
    check) for the identical state, and (b) propagates that same up-to-date
    verdict to anything depending on this file, which `make`'s own mtime
    check then never even visits (#841 D5 finding 5/Major-5).

    `prereqs` is the exact prerequisite list `rocq dep` reported for this
    file at the last real build (stored in the stamp) -- the file's own
    `.v`, every `Require`d library's `.vo`, every `Load`/plugin dependency --
    the SAME set `make`'s own `-include`d dependency file already uses to
    decide this target's staleness. The new mtime is bounded "restat"
    semantics (#841 Review841 G5, a real regression this design introduced
    in its original fix for finding 5/Major-5): `max` of those prerequisites'
    CURRENT mtimes, capped at `time.time()` so it can never read as being
    from the future, and applied only if that computed floor is strictly
    greater than the target's own CURRENT mtime. The prior version set every
    reused target's mtime to `max(now, every .vo under every -Q/-R dir) + 1`
    unconditionally: a chain of N reused files pushed mtimes N seconds into
    the future, and once wall-clock time caught up to an earlier link's
    artificially-future mtime, `make` would treat the whole tree as up to
    date even past a real breaking edit downstream. This version can never
    manufacture freshness beyond what the prerequisites and the real clock
    already support, and never moves a target that is already at least as
    new as everything it depends on.

    All arithmetic here is integer nanoseconds (#841 Review841 R1): a
    Python float mtime only resolves to ~238ns at current epoch values, so
    comparing/assigning via `os.path.getmtime`/`os.utime`'s float
    `(atime, mtime)` form could silently round a target's intended
    equal-or-newer mtime to BELOW a prerequisite's real mtime (observed:
    every B*.vo landing 46ns OLDER than A.vo despite the restat logic
    intending equal-or-newer), making `make` reinvoke this driver on every
    single no-op run. `st_mtime_ns`/`os.utime(..., ns=...)` keep every value
    an exact integer nanosecond count, so no such round-trip can occur.
    """
    mtimes_ns = []
    for path in prereqs:
        try:
            mtimes_ns.append(os.stat(path).st_mtime_ns)
        except OSError:
            pass
    if not mtimes_ns:
        return
    new_mtime_ns = min(max(mtimes_ns), time.time_ns())
    for target in (vo, glob):
        if not os.path.exists(target):
            continue
        if new_mtime_ns > os.stat(target).st_mtime_ns:
            os.utime(target, ns=(new_mtime_ns, new_mtime_ns))


def main() -> None:
    argv = sys.argv[1:]
    if not argv or argv[0] != "compile":
        # Not the compile sub-command (e.g. coqdep invokes `rocq dep`) --
        # not this driver's target, forward untouched.
        os.execv(REAL_ROCQ, [REAL_ROCQ] + argv)
        return  # pragma: no cover -- os.execv never returns except on error
    rest = argv[1:]
    classified = classify_compile(rest)
    if classified is None:
        # -vos/-vok/-vio/-beautify, or any other shape the cutoff logic
        # isn't sound for: bypass completely, no stamp read or write at all,
        # before any cutoff logic runs (#841 D5 finding 2/M2).
        os.execv(REAL_ROCQ, [REAL_ROCQ] + argv)
        return  # pragma: no cover -- os.execv never returns except on error
    flags, vfile = classified
    stem = vfile[: -len(".v")]
    vo = stem + ".vo"
    glob = stem + ".glob"
    stamp = stem + ".vo.cutoff-stamp"

    pre_hash = sha256_of(vfile)

    if not AGENT_INTERACTIVE:
        # Default BLOCKED: no caller has opted in, so always real-build --
        # even against a stamp that still matches (#841 D5, M3).
        log("SKIP-NOT-INTERACTIVE", vfile)
        real_build(flags, vfile, vo, stamp, pre_hash)
        return

    if not os.path.exists(vo) or not os.path.exists(stamp):
        real_build(flags, vfile, vo, stamp, pre_hash)
        return

    stamp_data = read_stamp(stamp)
    if stamp_data is None or stamp_data.get("v_hash") != pre_hash:
        real_build(flags, vfile, vo, stamp, pre_hash)
        return

    # G4: the stamp must still describe the .vo actually on disk. An
    # externally edited-then-reverted .v, or a hand-edited .vo (bypassing
    # this driver entirely), can leave a stamp whose v_hash matches the
    # reverted .v while the .vo no longer reflects what this driver last
    # produced -- that inconsistent state must force a real rebuild even
    # though the own-source check above passed.
    try:
        current_vo_hash = sha256_of(vo)
    except OSError:
        current_vo_hash = None
    if current_vo_hash is None or current_vo_hash != stamp_data.get("vo_hash"):
        log("REBUILD-VO-MISMATCH", vfile)
        real_build(flags, vfile, vo, stamp, pre_hash)
        return

    # G3: every Load/Extra Dependency/plugin prerequisite rocq dep listed
    # for this file at the last real build must still hash the same. A
    # stamp that couldn't record them (dep_hashes is None, e.g. `rocq dep`
    # itself failed at build time) can't confirm reuse either.
    dep_hashes = stamp_data.get("dep_hashes")
    if dep_hashes is None or not dep_hashes_match(dep_hashes):
        log("REBUILD-DEP-MISMATCH", vfile)
        real_build(flags, vfile, vo, stamp, pre_hash)
        return

    loadpath = parse_loadpath(flags)
    logical = derive_logical_name(vfile, loadpath)
    if logical is None:
        log("SKIP-NO-LOGICAL-NAME", vfile)
        real_build(flags, vfile, vo, stamp, pre_hash)
        return

    check_cmd = [COQTOP, "-batch"] + flags + ["-require", logical]
    r = subprocess.run(check_cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if r.returncode != 0:
        tail = r.stdout.decode("utf-8", "replace").strip().splitlines()[-1:]
        log("REBUILD-REFUSED", vfile, tail[0] if tail else "")
        real_build(flags, vfile, vo, stamp, pre_hash)
        return

    touch_reused_targets(vo, glob, stamp_data.get("prereqs") or [])
    log("REUSED", vfile)


if __name__ == "__main__":
    main()
