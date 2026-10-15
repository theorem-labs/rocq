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
     (a `<file>.vo.cutoff-stamp` sidecar). Missing stamp, missing .vo, or a
     hash mismatch -> always a real compile. (v1 hashed AFTER `subprocess.run`
     returned and wrote that re-derived value -- a TOCTOU: an edit landing
     during the compile got recorded against the OLD .vo. Fixed by capturing
     `pre_hash` exactly once and never re-deriving it.)
  2. Interactive gate: the cutoff (reuse) logic below is only reachable when
     `CUTOFF_AGENT_INTERACTIVE=1` is set in the environment; otherwise this
     driver always real-builds, unconditionally, even against a matching
     stamp. v1 had this inverted (`BET_GRADING`, an opt-OUT nothing ever set,
     so the guard was inert by construction); this fails closed for any
     caller that doesn't explicitly opt in instead.
  3. Cheap acceptance check (only reached when the own source is unchanged
     and the caller opted in, i.e. make invoked us only because some
     dependency's .vo got a newer mtime): derive this file's logical (dotted)
     module name from the -Q/-R bindings in the same argv coq_makefile
     already built, and ask a throwaway `coqtop -batch ... -require <logical>`
     whether the existing .vo is still loadable. This is exactly Rocq's own
     Require-time consistency check (vernac/library.ml's file-level gate +
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
     never settled and every later `make` re-ran the same cheap check.
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


def real_build(flags: list[str], vfile: str, stamp: str, pre_hash: str) -> None:
    """Run the real compiler. `pre_hash` MUST be the sha256 of `vfile`
    captured before this call, and is written to the stamp verbatim, never
    re-derived -- #841 D5 / BugFinderRedTeamV2 M1: hashing again after
    `subprocess.run` returns can record a hash that doesn't match what was
    actually fed to the compiler, if `vfile` changed mid-compile.
    """
    cmd = [REAL_ROCQ, "compile"] + flags + [vfile]
    r = subprocess.run(cmd)
    if r.returncode == 0:
        Path(stamp).write_text(pre_hash)
        log("REBUILD", vfile)
    else:
        log("FAIL", vfile, str(r.returncode))
    sys.exit(r.returncode)


def touch_reused_targets(vo: str, glob: str, vfile: str, loadpath: list[tuple[str, str, str]]) -> None:
    """After a REUSED verdict, freshen every target CoqMakefile.in's grouped
    `$(1).vo $(1).glob &: $(1).v` rule normally produces, WITHOUT rewriting
    their bytes, so a subsequent `make` (a) considers this target up to date
    and never re-invokes this driver (never re-runs the `coqtop -require`
    check) for the identical state, and (b) propagates that same up-to-date
    verdict to anything depending on this file, which `make`'s own mtime
    check then never even visits (#841 D5 finding 5/Major-5).

    Known limitation, not fully closed (BugFinderRedTeamV2 M2): `make`'s own
    prerequisite-mtime staleness check -- not this driver -- decides whether
    the driver is invoked at all, and that check knows nothing about content
    hashes. Touching a target's mtime forward can make a LATER genuine edit
    to `vfile` invisible to `make` if the edited file's own resulting mtime
    ever ends up older than the touched target (clock skew, a timestamp-
    preserving cache restore). This is the known cost of layering a hash-
    based cutoff under a pure-mtime build system; it is mitigated here, not
    eliminated, by choosing a new mtime strictly greater than every
    prerequisite CURRENTLY on disk (not just the targets' own old mtime):
    `vfile` itself, and every `.vo` reachable under the `-Q`/`-R` physical
    directories -- the only prerequisites this driver can structurally name.
    """
    candidates = [time.time(), os.path.getmtime(vfile)]
    seen_dirs: set[str] = set()
    for _kind, physdir, _logical in loadpath:
        pd = os.path.normpath(physdir)
        if pd in seen_dirs:
            continue
        seen_dirs.add(pd)
        for dirpath, _dirnames, filenames in os.walk(pd):
            for name in filenames:
                if name.endswith(".vo"):
                    try:
                        candidates.append(os.path.getmtime(os.path.join(dirpath, name)))
                    except OSError:
                        pass
    new_mtime = max(candidates) + 1
    for target in (vo, glob):
        if os.path.exists(target):
            os.utime(target, (new_mtime, new_mtime))


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
        real_build(flags, vfile, stamp, pre_hash)
        return

    if not os.path.exists(vo) or not os.path.exists(stamp):
        real_build(flags, vfile, stamp, pre_hash)
        return

    if Path(stamp).read_text().strip() != pre_hash:
        real_build(flags, vfile, stamp, pre_hash)
        return

    loadpath = parse_loadpath(flags)
    logical = derive_logical_name(vfile, loadpath)
    if logical is None:
        log("SKIP-NO-LOGICAL-NAME", vfile)
        real_build(flags, vfile, stamp, pre_hash)
        return

    check_cmd = [COQTOP, "-batch"] + flags + ["-require", logical]
    r = subprocess.run(check_cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if r.returncode != 0:
        tail = r.stdout.decode("utf-8", "replace").strip().splitlines()[-1:]
        log("REBUILD-REFUSED", vfile, tail[0] if tail else "")
        real_build(flags, vfile, stamp, pre_hash)
        return

    touch_reused_targets(vo, glob, vfile, loadpath)
    log("REUSED", vfile)


if __name__ == "__main__":
    main()
