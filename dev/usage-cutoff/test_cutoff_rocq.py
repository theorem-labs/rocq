"""Pytest suite for `dev/usage-cutoff/cutoff_rocq.py`'s own argv/stamp logic
(binary-equivalence-taiga#841 D5/D6; the driver findings from rocq#10's two
reviews and BugFinderRedTeamV2's hardening pass: finding 2/M2, Major-5, m4,
M1-M4; and Review841's G3/G4/G5, issuecomment-6187211433). Every reproduction
here is a direct test of the driver's own argv parsing and stamp bookkeeping,
not of Rocq itself: `subprocess.run` is mocked throughout, so there is no
network dependency and no real `rocq`/`coqtop` binary is ever invoked.

Since G3/G4/G5, every REAL build also shells out to `rocq dep` once (to learn
the file's own Load/Extra Dependency/plugin prerequisites and populate the
stamp), so most `subprocess.run` mocks here now dispatch on `cmd[1]`
(`"compile"` vs `"dep"`) rather than assuming a single call.
"""
import hashlib
import importlib.util
import json
import os
import sys
import time
from pathlib import Path
from unittest.mock import MagicMock

import pytest

_MODULE_PATH = Path(__file__).resolve().parent / "cutoff_rocq.py"
_spec = importlib.util.spec_from_file_location("cutoff_rocq", _MODULE_PATH)
assert _spec is not None and _spec.loader is not None
cutoff_rocq = importlib.util.module_from_spec(_spec)
sys.modules["cutoff_rocq"] = cutoff_rocq
_spec.loader.exec_module(cutoff_rocq)


def _fake_completed(returncode: int = 0, stdout: bytes = b"") -> MagicMock:
    proc = MagicMock()
    proc.returncode = returncode
    proc.stdout = stdout
    return proc


def _write_source(tmp_path: Path, name: str = "Foo.v") -> Path:
    vfile = tmp_path / name
    vfile.write_text("Definition x := 1.\n")
    return vfile


def _write_stamp(path: Path, *, v_hash: str, vo_hash=None, dep_hashes=None, prereqs=None) -> None:
    path.write_text(
        json.dumps({"v_hash": v_hash, "vo_hash": vo_hash, "dep_hashes": dep_hashes, "prereqs": prereqs})
    )


def _read_stamp(path: Path) -> dict:
    return json.loads(path.read_text())


def _dep_line(vfile: str, deps: list[str] = ()) -> bytes:
    """A `rocq dep`-shaped Make-rule line for `vfile`, exactly the format
    `tools/coqdep/lib/makefile.ml`'s `print_dep` emits, with `vfile` itself
    plus `deps` as the prerequisite list."""
    stem = vfile[: -len(".v")]
    tokens = [vfile, *deps]
    line = f"{stem}.vo {stem}.glob {stem}.v.beautified {stem}.required_vo: " + " ".join(tokens) + "\n"
    return line.encode()


class TestVosVokBeautifyBypass:
    """(a) a -vos/-vok (and -vio/-beautify) invocation never touches the
    stamp file at all -- #841 D5 finding 2/M2. v1's dispatch only checked
    `argv[0] != "compile"`, which does not catch these: they are flags
    inside `compile`'s own argv, not a different subcommand.
    """

    @pytest.mark.parametrize("flag", ["-vos", "-vok", "-vio", "-beautify"])
    def test_bypass_no_stamp_or_hash(self, tmp_path, monkeypatch, flag):
        vfile = _write_source(tmp_path)
        stamp = tmp_path / "Foo.vo.cutoff-stamp"

        execv_calls = []

        def fake_execv(path, args):
            execv_calls.append((path, args))
            raise SystemExit(0)

        monkeypatch.setattr(cutoff_rocq.os, "execv", fake_execv)

        sha_calls = []
        monkeypatch.setattr(
            cutoff_rocq, "sha256_of", lambda p: sha_calls.append(p) or "deadbeef"
        )

        run_mock = MagicMock(
            side_effect=AssertionError("subprocess.run must not run for a non-.vo pass")
        )
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)

        argv = ["compile", flag, "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit):
            cutoff_rocq.main()

        assert not stamp.exists(), "the stamp must not exist after a bypassed pass"
        assert sha_calls == [], "the source must never be hashed for a bypassed pass"
        run_mock.assert_not_called()
        assert len(execv_calls) == 1
        exec_path, exec_args = execv_calls[0]
        assert exec_path == cutoff_rocq.REAL_ROCQ
        assert exec_args == [cutoff_rocq.REAL_ROCQ, *argv]

    def test_unknown_future_flag_also_bypasses(self, tmp_path, monkeypatch):
        """BugFinderRedTeamV2 M4: the structural check must fail toward MORE
        bypassing for any flag outside the known-safe set, not just the four
        named today -- otherwise a future Rocq flag in the same family
        reopens finding 2 silently.
        """
        vfile = _write_source(tmp_path)
        stamp = tmp_path / "Foo.vo.cutoff-stamp"

        monkeypatch.setattr(
            cutoff_rocq.os,
            "execv",
            lambda path, args: (_ for _ in ()).throw(SystemExit(0)),
        )
        sha_mock = MagicMock()
        monkeypatch.setattr(cutoff_rocq, "sha256_of", sha_mock)
        argv = ["compile", "-some-brand-new-flag", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit):
            cutoff_rocq.main()

        assert not stamp.exists()
        sha_mock.assert_not_called()


class TestHashBeforeCompile:
    """(b) the stamp's `v_hash` records the hash captured BEFORE the real
    compiler runs, never a value re-derived afterward -- #841 D5 /
    BugFinderRedTeamV2 M1. v1 hashed again after `subprocess.run` returned,
    a TOCTOU: an edit landing during the compile got recorded against the
    stale `.vo`. #841 Review841 G3/G4 added two more stamp fields
    (`vo_hash`, `dep_hashes`/`prereqs`) computed AFTER the compile, from the
    freshly produced `.vo` and `rocq dep`'s own prerequisite list for this
    file -- this test checks those don't disturb the one invariant M1 fixed:
    `vfile` itself is still hashed exactly once, before the compiler runs,
    and is never re-hashed a second time even via the new G3 dependency set
    (which always lists the file's own `.v` as its first prerequisite).
    """

    def test_first_hash_wins_even_if_file_changes_during_compile(self, tmp_path, monkeypatch):
        vfile = _write_source(tmp_path)
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        vo = tmp_path / "Foo.vo"

        sha_calls: list[str] = []

        def fake_sha256_of(p):
            sha_calls.append(p)
            if p == str(vfile):
                return "pre-compile-hash"
            if p == str(vo):
                return "vo-hash"
            raise AssertionError(f"unexpected sha256_of call for {p}")

        monkeypatch.setattr(cutoff_rocq, "sha256_of", fake_sha256_of)

        def fake_run(cmd, **kwargs):
            if cmd[0] == cutoff_rocq.REAL_ROCQ and cmd[1] == "compile":
                # Simulate the compiler (or a concurrent edit) changing what
                # a naive post-hoc re-hash would see.
                vo.write_bytes(b"compiled")
                return _fake_completed(returncode=0)
            if cmd[0] == cutoff_rocq.REAL_ROCQ and cmd[1] == "dep":
                return _fake_completed(returncode=0, stdout=_dep_line(str(vfile)))
            raise AssertionError(f"unexpected subprocess.run call: {cmd}")

        monkeypatch.setattr(cutoff_rocq.subprocess, "run", fake_run)
        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", False)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit) as exc_info:
            cutoff_rocq.main()
        assert exc_info.value.code == 0

        vfile_calls = [p for p in sha_calls if p == str(vfile)]
        assert vfile_calls == [str(vfile)], "the source must be hashed exactly once, before compiling"

        stamp_data = _read_stamp(stamp)
        assert stamp_data["v_hash"] == "pre-compile-hash"
        assert stamp_data["vo_hash"] == "vo-hash"
        # The dep line's only prerequisite is vfile itself, already covered
        # by v_hash -- G3/G4 must not hash it a second time (that would be
        # exactly the post-compile re-read M1 eliminated, just for a new
        # field).
        assert stamp_data["dep_hashes"] == {}
        assert stamp_data["prereqs"] == [str(vfile)]


class TestInteractiveGateDefaultBlocked:
    """(c) without CUTOFF_AGENT_INTERACTIVE=1, a matching stamp is still
    ignored and a real build is forced -- #841 D5 / BugFinderRedTeamV2 M3.
    v1's guard (`BET_GRADING`) was an opt-OUT nothing ever set, so it was
    inert; the fix defaults BLOCKED and requires an explicit opt-in instead.
    """

    def test_matching_stamp_ignored_when_not_opted_in(self, tmp_path, monkeypatch):
        vfile = _write_source(tmp_path)
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"stale-but-matching")
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        _write_stamp(
            stamp,
            v_hash=hashlib.sha256(vfile.read_bytes()).hexdigest(),
            vo_hash=hashlib.sha256(b"stale-but-matching").hexdigest(),
        )

        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", False)
        run_mock = MagicMock(return_value=_fake_completed(returncode=0))
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit) as exc_info:
            cutoff_rocq.main()
        assert exc_info.value.code == 0

        # Two subprocess calls -- the real compile and its own `rocq dep`
        # prerequisite scan for the new stamp -- and no coqtop `-require`
        # check at all: the interactive gate must short-circuit before the
        # stamp is even consulted.
        assert run_mock.call_count == 2
        for call in run_mock.call_args_list:
            cmd = call.args[0]
            assert cmd[0] == cutoff_rocq.REAL_ROCQ
            assert cutoff_rocq.COQTOP not in cmd
        assert run_mock.call_args_list[0].args[0][1] == "compile"
        assert run_mock.call_args_list[1].args[0][1] == "dep"


class TestInteractiveReuseAcceptance:
    """(d) with CUTOFF_AGENT_INTERACTIVE=1 set, a matching stamp triggers the
    cheap `coqtop -require` acceptance check instead of a real compile. The
    REUSE decision path itself never shells out to `rocq dep` again -- the
    prerequisite set is fixed once a build's `.v` content is fixed, so it is
    read back from the stamp instead of recomputed.
    """

    def test_matching_stamp_triggers_coqtop_check(self, tmp_path, monkeypatch):
        vfile = _write_source(tmp_path)
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"up-to-date")
        glob = tmp_path / "Foo.glob"
        glob.write_bytes(b"")
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        _write_stamp(
            stamp,
            v_hash=hashlib.sha256(vfile.read_bytes()).hexdigest(),
            vo_hash=hashlib.sha256(vo.read_bytes()).hexdigest(),
            dep_hashes={},
            prereqs=[],
        )

        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", True)
        run_mock = MagicMock(return_value=_fake_completed(returncode=0, stdout=b""))
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        cutoff_rocq.main()  # REUSED verdict: no sys.exit at all

        run_mock.assert_called_once()
        cmd = run_mock.call_args[0][0]
        assert cmd[0] == cutoff_rocq.COQTOP
        assert "-batch" in cmd
        assert "-require" in cmd
        assert cmd[cmd.index("-require") + 1] == "Lib.Foo"

        # Bytes stay exactly as they were -- only mtimes may move, and since
        # `prereqs` is empty here there is nothing to float the mtime to.
        assert vo.read_bytes() == b"up-to-date"
        assert glob.read_bytes() == b""
        assert _read_stamp(stamp)["v_hash"] == hashlib.sha256(vfile.read_bytes()).hexdigest()

    def test_coqtop_refusal_forces_real_build(self, tmp_path, monkeypatch):
        """The opposite verdict: the kernel's own cheap check refuses reuse,
        and the driver must forward that refusal into a real rebuild, not
        silently keep the stale `.vo` (#841 D5 Major-5 risk inverted: a
        driver that hardcodes REUSED would also pass every "reuse works"
        test; this is the one that catches a hardcoded/inverted verdict).
        """
        vfile = _write_source(tmp_path)
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"stale")
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        _write_stamp(
            stamp,
            v_hash=hashlib.sha256(vfile.read_bytes()).hexdigest(),
            vo_hash=hashlib.sha256(b"stale").hexdigest(),
            dep_hashes={},
            prereqs=[],
        )

        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", True)

        def fake_run(cmd, **kwargs):
            if cmd[0] == cutoff_rocq.COQTOP:
                return _fake_completed(returncode=1, stdout=b"Error: inconsistent assumptions\n")
            if cmd[0] == cutoff_rocq.REAL_ROCQ and cmd[1] == "dep":
                return _fake_completed(returncode=0, stdout=_dep_line(str(vfile)))
            return _fake_completed(returncode=0)

        run_mock = MagicMock(side_effect=fake_run)
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit) as exc_info:
            cutoff_rocq.main()
        assert exc_info.value.code == 0

        assert run_mock.call_count == 3  # the coqtop check, the real compile, its own rocq dep scan
        real_compile_calls = [
            c for c in run_mock.call_args_list if c.args[0][0] == cutoff_rocq.REAL_ROCQ and c.args[0][1] == "compile"
        ]
        assert len(real_compile_calls) == 1


class TestCoqdepOutputParsing:
    """Unit coverage for the `rocq dep` output parser backing #841
    Review841 G3/G5 -- `parse_coqdep_deps` and `extract_dep_flags`.
    """

    def test_parses_simple_rule_line(self):
        output = "Foo.vo Foo.glob Foo.v.beautified Foo.required_vo: Foo.v Bar.vo plugin.cma plugin.cmxs Other.v\n"
        assert cutoff_rocq.parse_coqdep_deps(output) == [
            "Foo.v",
            "Bar.vo",
            "plugin.cma",
            "plugin.cmxs",
            "Other.v",
        ]

    def test_unescapes_backslash_escaped_space(self):
        output = "Foo.vo: Foo.v a\\ b.v\n"
        assert cutoff_rocq.parse_coqdep_deps(output) == ["Foo.v", "a b.v"]

    def test_unescapes_doubled_dollar(self):
        output = "Foo.vo: Foo.v plugin$$cutoff.cma\n"
        assert cutoff_rocq.parse_coqdep_deps(output) == ["Foo.v", "plugin$cutoff.cma"]

    def test_empty_output_parses_to_empty_list(self):
        assert cutoff_rocq.parse_coqdep_deps("") == []

    def test_extract_dep_flags_keeps_only_loadpath_flags(self):
        flags = [
            "-Q", "/a", "Lib",
            "-w", "0",
            "-native-compiler", "ondemand",
            "-q",
            "-I", "/b",
            "-time-file", "foo.timing",
        ]
        assert cutoff_rocq.extract_dep_flags(flags) == ["-Q", "/a", "Lib", "-I", "/b"]


class TestDepHashesMatch:
    """Unit coverage for `dep_hashes_match`, the #841 Review841 G3 re-check."""

    def test_empty_dict_trivially_matches(self):
        assert cutoff_rocq.dep_hashes_match({}) is True

    def test_missing_file_counts_as_mismatch(self, tmp_path):
        assert cutoff_rocq.dep_hashes_match({str(tmp_path / "missing.v"): "whatever"}) is False

    def test_content_mismatch_detected(self, tmp_path):
        f = tmp_path / "A.v"
        f.write_text("x")
        assert cutoff_rocq.dep_hashes_match({str(f): "wrong-hash"}) is False
        assert cutoff_rocq.dep_hashes_match({str(f): hashlib.sha256(b"x").hexdigest()}) is True


class TestDependencyContentChangeForcesRebuild:
    """#841 Review841 G3: the stamp hashing only the `.v` file missed
    `Load`/`Extra Dependency`/plugin prerequisites coqdep already lists.
    Reproduces the `ld` experiment: the main file's own bytes are unchanged,
    but a `Load`ed dependency's content changed -- that alone must force a
    real rebuild, never reach the cheap coqtop check.
    """

    def test_changed_load_dependency_forces_rebuild(self, tmp_path, monkeypatch):
        vfile = _write_source(tmp_path)
        other = tmp_path / "Other.v"
        other.write_text("Definition y := 1.\n")
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"up-to-date")
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        _write_stamp(
            stamp,
            v_hash=hashlib.sha256(vfile.read_bytes()).hexdigest(),
            vo_hash=hashlib.sha256(vo.read_bytes()).hexdigest(),
            # Recorded at a prior build, before Other.v was edited.
            dep_hashes={str(other): "stale-hash-from-before-the-edit"},
            prereqs=[str(vfile), str(other)],
        )

        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", True)

        def fake_run(cmd, **kwargs):
            if cmd[0] == cutoff_rocq.COQTOP:
                raise AssertionError(
                    "the cheap coqtop check must never run once a Load/plugin dependency's content changed"
                )
            if cmd[0] == cutoff_rocq.REAL_ROCQ and cmd[1] == "dep":
                return _fake_completed(returncode=0, stdout=_dep_line(str(vfile), [str(other)]))
            return _fake_completed(returncode=0)

        run_mock = MagicMock(side_effect=fake_run)
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit) as exc_info:
            cutoff_rocq.main()
        assert exc_info.value.code == 0

        compile_calls = [
            c for c in run_mock.call_args_list if c.args[0][0] == cutoff_rocq.REAL_ROCQ and c.args[0][1] == "compile"
        ]
        assert len(compile_calls) == 1, "a changed Load/plugin dependency must force a real rebuild"

    def test_unchanged_dependencies_allow_reuse(self, tmp_path, monkeypatch):
        """Control for the test above: the identical fixture, but with the
        CORRECT stored hash for `Other.v`, reaches the coqtop check and
        reuses -- proving the failure above is a real content check, not
        reuse being unconditionally broken.
        """
        vfile = _write_source(tmp_path)
        other = tmp_path / "Other.v"
        other.write_text("Definition y := 1.\n")
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"up-to-date")
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        _write_stamp(
            stamp,
            v_hash=hashlib.sha256(vfile.read_bytes()).hexdigest(),
            vo_hash=hashlib.sha256(vo.read_bytes()).hexdigest(),
            dep_hashes={str(other): hashlib.sha256(other.read_bytes()).hexdigest()},
            prereqs=[str(vfile), str(other)],
        )

        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", True)
        run_mock = MagicMock(return_value=_fake_completed(returncode=0, stdout=b""))
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        cutoff_rocq.main()  # REUSED verdict: no sys.exit at all

        run_mock.assert_called_once()
        assert run_mock.call_args[0][0][0] == cutoff_rocq.COQTOP


class TestVoDesyncForcesRebuild:
    """#841 Review841 G4: the stamp isn't bound to the `.vo` it claims to
    describe. Reproduces Review841's `st` experiment: build M, hand-edit
    M.v, compile by hand (bypassing the driver, so no stamp update), then
    revert M.v -- the stamp still matches M.v's reverted hash, but M.vo now
    reflects the hand-edit and must not be reused.
    """

    def test_vo_hash_mismatch_forces_rebuild_even_with_matching_source(self, tmp_path, monkeypatch):
        vfile = _write_source(tmp_path)
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"hand-edited-out-of-band")
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        # v_hash matches the CURRENT (reverted) .v exactly, but vo_hash was
        # recorded against a DIFFERENT .vo than the one now on disk.
        _write_stamp(
            stamp,
            v_hash=hashlib.sha256(vfile.read_bytes()).hexdigest(),
            vo_hash=hashlib.sha256(b"the-original-driver-built-vo").hexdigest(),
            dep_hashes={},
            prereqs=[],
        )

        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", True)

        def fake_run(cmd, **kwargs):
            if cmd[0] == cutoff_rocq.COQTOP:
                raise AssertionError(
                    "the cheap coqtop check must never run once the .vo is desynced from its own stamp"
                )
            if cmd[0] == cutoff_rocq.REAL_ROCQ and cmd[1] == "dep":
                return _fake_completed(returncode=0, stdout=_dep_line(str(vfile)))
            return _fake_completed(returncode=0)

        run_mock = MagicMock(side_effect=fake_run)
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit) as exc_info:
            cutoff_rocq.main()
        assert exc_info.value.code == 0

        compile_calls = [
            c for c in run_mock.call_args_list if c.args[0][0] == cutoff_rocq.REAL_ROCQ and c.args[0][1] == "compile"
        ]
        assert len(compile_calls) == 1, "a .vo that doesn't match its own stamp must force a real rebuild"

    def test_missing_vo_hash_in_stamp_forces_rebuild(self, tmp_path, monkeypatch):
        """A stamp with no `vo_hash` to compare against (written before G4,
        or one whose vo_hash computation failed at build time) must also
        fail closed into a rebuild, not be treated as "nothing to check".
        """
        vfile = _write_source(tmp_path)
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"some-vo")
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        _write_stamp(
            stamp,
            v_hash=hashlib.sha256(vfile.read_bytes()).hexdigest(),
            vo_hash=None,
            dep_hashes={},
            prereqs=[],
        )

        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", True)

        def fake_run(cmd, **kwargs):
            if cmd[0] == cutoff_rocq.COQTOP:
                raise AssertionError("must not reach the coqtop check without a vo_hash to confirm")
            if cmd[0] == cutoff_rocq.REAL_ROCQ and cmd[1] == "dep":
                return _fake_completed(returncode=0, stdout=_dep_line(str(vfile)))
            return _fake_completed(returncode=0)

        run_mock = MagicMock(side_effect=fake_run)
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit):
            cutoff_rocq.main()

        compile_calls = [
            c for c in run_mock.call_args_list if c.args[0][0] == cutoff_rocq.REAL_ROCQ and c.args[0][1] == "compile"
        ]
        assert len(compile_calls) == 1


class TestBoundedMtimeRestat:
    """#841 Review841 G5: `touch_reused_targets` must restat each reused
    target to the max of its OWN prerequisites' CURRENT mtimes, never above
    real wall-clock time, and never touch a target already at least as new
    as those prerequisites -- not the prior unconditional
    `max(now, every .vo under -Q/-R) + 1` ratchet, which pushed every reused
    target N seconds into the future across an N-file reuse chain.
    """

    def test_touches_forward_to_max_prerequisite_mtime(self, tmp_path, monkeypatch):
        vo = tmp_path / "Foo.vo"
        glob = tmp_path / "Foo.glob"
        vo.write_bytes(b"vo")
        glob.write_bytes(b"glob")
        dep = tmp_path / "Dep.vo"
        dep.write_bytes(b"dep")

        old = time.time() - 1000
        os.utime(vo, (old, old))
        os.utime(glob, (old, old))
        dep_mtime = time.time() - 10
        os.utime(dep, (dep_mtime, dep_mtime))

        fixed_now = time.time() + 10_000  # far ahead of dep_mtime
        monkeypatch.setattr(cutoff_rocq.time, "time", lambda: fixed_now)

        cutoff_rocq.touch_reused_targets(str(vo), str(glob), [str(dep)])

        # The new mtime is exactly the prerequisite's mtime -- NOT `now`,
        # and NOT `now + 1`: restat to own prerequisites, never an
        # unconditional forward push to wall-clock time.
        assert os.path.getmtime(vo) == pytest.approx(dep_mtime, abs=1e-3)
        assert os.path.getmtime(glob) == pytest.approx(dep_mtime, abs=1e-3)

    def test_never_exceeds_real_time_even_if_a_prerequisite_is_in_the_future(self, tmp_path, monkeypatch):
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"vo")
        old = time.time() - 1000
        os.utime(vo, (old, old))

        dep = tmp_path / "Dep.vo"
        dep.write_bytes(b"dep")
        future_mtime = time.time() + 5000  # clock-skew-style future prerequisite
        os.utime(dep, (future_mtime, future_mtime))

        fixed_now = time.time() + 1  # real time is far earlier than the skewed prerequisite
        monkeypatch.setattr(cutoff_rocq.time, "time", lambda: fixed_now)

        cutoff_rocq.touch_reused_targets(str(vo), str(vo), [str(dep)])

        assert os.path.getmtime(vo) == pytest.approx(fixed_now, abs=1e-3)
        assert os.path.getmtime(vo) < future_mtime

    def test_does_not_touch_a_target_already_at_least_as_new(self, tmp_path, monkeypatch):
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"vo")
        dep = tmp_path / "Dep.vo"
        dep.write_bytes(b"dep")

        now = time.time()
        os.utime(dep, (now - 100, now - 100))
        os.utime(vo, (now - 10, now - 10))  # already newer than its only prerequisite

        utime_calls = []
        monkeypatch.setattr(cutoff_rocq.os, "utime", lambda *a, **k: utime_calls.append(a))

        cutoff_rocq.touch_reused_targets(str(vo), str(vo), [str(dep)])

        assert utime_calls == [], "a target already up to date relative to its own prerequisites must not be touched"

    def test_no_ratchet_across_a_reuse_chain(self, tmp_path, monkeypatch):
        """Review841's `mt` repro, directly: a chain of reused files
        A..I where each link's only prerequisite is the previous link. The
        prior `max(now, ...) + 1` fix incremented every link's mtime one
        second past the last, drifting the whole chain ahead of wall-clock
        time link by link; the fix here must settle every link at exactly
        the mtime of the one genuine rebuild (A) that started the chain,
        never incrementing further down the chain and never exceeding real
        time.
        """
        fixed_now = time.time() + 100  # keep "now" comfortably ahead of everything below
        monkeypatch.setattr(cutoff_rocq.time, "time", lambda: fixed_now)

        files = [tmp_path / f"{letter}.vo" for letter in "ABCDEFGHI"]
        base = fixed_now - 1000
        for f in files:
            f.write_bytes(b"x")
            os.utime(f, (base, base))

        # A gets a genuine fresh rebuild, newer than everything downstream.
        rebuilt = base + 5
        os.utime(files[0], (rebuilt, rebuilt))

        for prev, cur in zip(files, files[1:]):
            cutoff_rocq.touch_reused_targets(str(cur), str(cur), [str(prev)])

        # Every link in the chain settles at exactly A's rebuilt mtime --
        # never incremented link over link (the old `+1` ratchet would have
        # left the last link 7 seconds ahead of A), and never above "now".
        for f in files:
            assert os.path.getmtime(f) == pytest.approx(rebuilt, abs=1e-3)
            assert os.path.getmtime(f) <= fixed_now + 1e-6
