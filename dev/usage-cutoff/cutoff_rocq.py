#!/usr/bin/env python3
"""Drop-in replacement for the `rocq` binary coq_makefile's generated Makefile
invokes as `$(ROCQ) compile <flags...> <file.v>` (ROCQ ?= "$(COQBIN)rocq").

The usage-cutoff fork's loader already accepts a dependent .vo whose own
source is unchanged, against a rebuilt dependency, whenever the per-declaration
interface subset it recorded still matches (Admitted->Qed, an unused addition).
coq_makefile's generated rules only ever check *mtimes*: a target is rebuilt
whenever any of its direct-dependency .vo files is newer, with no reference to
whether the fork would actually refuse it. This wrapper closes that gap:

  1. Own-source check (never skipped): compare the current sha256 of the .v
     file being "compiled" against the hash recorded the last time this
     wrapper actually ran a real compile (a `<file>.vo.cutoff-stamp` sidecar).
     Missing stamp, missing .vo, or a hash mismatch -> always a real compile.
  2. Cheap acceptance check (only reached when the own source is unchanged,
     i.e. make invoked us only because some dependency's .vo got a newer
     mtime): derive this file's logical (dotted) module name from the -Q/-R
     bindings in the same argv coq_makefile already built, and ask a throwaway
     `coqtop -batch ... -require <logical>` whether the existing .vo is still
     loadable. This is exactly Rocq's own Require-time consistency check
     (vernac/library.ml's file-level gate + kernel/safe_typing.ml's
     check_required) with none of the proof elaboration a real compile would
     redo -- cheap by construction, not by sampling.
  3. If step 2 accepts: do *nothing* to the .vo/.glob (no touch, no rewrite).
     Make considers the recipe "done" but the target's mtime is unchanged, so
     anything that in turn depends on *this* file sees no new mtime and is
     never even visited by coq_makefile's own mtime check -- the cutoff
     composes correctly across chains with no extra bookkeeping.
  4. If step 2 refuses (or anything about it is inconclusive: a nested
     module/functor the fork's interface table can't represent, step-2's own
     subprocess failing to start, etc.): fall back to a real compile. This is
     the fail-safe direction -- never skip when unsure, only ever skip when a
     cheap, explicit check proved the fork would already have proved reuse
     safe.

Every result this driver reuses is one the fork's own loader and, at grade
time, coqchk, independently re-verify (CARRY-BUILD-PROTO.md's "coqchk is the
trust anchor" and this fork's own Require-time gate: see ROCQ-USAGE-CUTOFF.md
S4). This driver changes nothing about what gets *proof-checked* -- only what
gets *recompiled*.
"""
import hashlib
import os
import subprocess
import sys
from pathlib import Path

REAL_ROCQ = os.environ.get(
    "CUTOFF_REAL_ROCQ", "/rocq/rocq-usage-cutoff/_build/install/default/bin/rocq"
)
COQTOP = os.environ.get(
    "CUTOFF_COQTOP", os.path.join(os.path.dirname(REAL_ROCQ), "coqtop")
)
STATS_LOG = os.environ.get("CUTOFF_STATS_LOG")
# Set to "1" to disable the cutoff entirely (always real-build) -- used by the
# (b) arm of the three-way replay ("the fork plus today's make, no driver").
DISABLE = os.environ.get("CUTOFF_DISABLE") == "1"


def log(kind: str, vfile: str, extra: str = "") -> None:
    if STATS_LOG:
        with open(STATS_LOG, "a") as f:
            f.write(f"{kind}\t{vfile}\t{extra}\n")


def sha256_of(path: str) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def derive_logical_name(vfile: str, loadpath: list[tuple[str, str, str]]) -> str | None:
    """loadpath: list of (kind, physdir, logical) from -Q/-R flags, in argv order."""
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


def real_build(flags: list[str], vfile: str, stamp: str) -> None:
    cmd = [REAL_ROCQ, "compile"] + flags + [vfile]
    r = subprocess.run(cmd)
    if r.returncode == 0:
        Path(stamp).write_text(sha256_of(vfile))
        log("REBUILD", vfile)
    else:
        log("FAIL", vfile, str(r.returncode))
    sys.exit(r.returncode)


def main() -> None:
    argv = sys.argv[1:]
    if not argv or argv[0] != "compile":
        # Not the compile sub-command (e.g. coqdep invokes `rocq dep`, or a
        # -vos/-vok pass) -- not this driver's target, forward untouched.
        os.execv(REAL_ROCQ, [REAL_ROCQ] + argv)
    rest = argv[1:]
    if not rest:
        os.execv(REAL_ROCQ, [REAL_ROCQ] + argv)
    vfile = rest[-1]
    flags = rest[:-1]
    stem = vfile[:-2] if vfile.endswith(".v") else vfile
    vo = stem + ".vo"
    stamp = stem + ".vo.cutoff-stamp"

    if DISABLE or not os.path.exists(vo) or not os.path.exists(stamp):
        real_build(flags, vfile, stamp)
        return

    if Path(stamp).read_text().strip() != sha256_of(vfile):
        real_build(flags, vfile, stamp)
        return

    loadpath = parse_loadpath(flags)
    logical = derive_logical_name(vfile, loadpath)
    if logical is None:
        log("SKIP-NO-LOGICAL-NAME", vfile)
        real_build(flags, vfile, stamp)
        return

    check_cmd = [COQTOP, "-batch"] + flags + ["-require", logical]
    r = subprocess.run(check_cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if r.returncode == 0:
        log("REUSED", vfile)
        return
    log("REBUILD-REFUSED", vfile, r.stdout.decode("utf-8", "replace").strip().splitlines()[-1:] and
        r.stdout.decode("utf-8", "replace").strip().splitlines()[-1])
    real_build(flags, vfile, stamp)


if __name__ == "__main__":
    main()
