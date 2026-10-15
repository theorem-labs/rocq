"""Pytest suite for `dev/usage-cutoff/cutoff_rocq.py`'s own argv/stamp logic
(binary-equivalence-taiga#841 D5/D6; the driver findings from rocq#10's two
reviews and BugFinderRedTeamV2's hardening pass: finding 2/M2, Major-5, m4,
M1-M4). Every reproduction here is a direct test of the driver's own argv
parsing and stamp bookkeeping, not of Rocq itself: `subprocess.run` is mocked
throughout, so there is no network dependency and no real `rocq`/`coqtop`
binary is ever invoked.
"""
import hashlib
import importlib.util
import sys
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
    """(b) the stamp records the hash captured BEFORE the real compiler
    runs, never a value re-derived afterward -- #841 D5 / BugFinderRedTeamV2
    M1. v1 hashed again after `subprocess.run` returned, a TOCTOU: an edit
    landing during the compile got recorded against the stale `.vo`.
    """

    def test_first_hash_wins_even_if_file_changes_during_compile(self, tmp_path, monkeypatch):
        vfile = _write_source(tmp_path)
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        vo = tmp_path / "Foo.vo"

        hashes = iter(["pre-compile-hash", "post-compile-hash-must-never-be-written"])
        sha_mock = MagicMock(side_effect=lambda _p: next(hashes))
        monkeypatch.setattr(cutoff_rocq, "sha256_of", sha_mock)

        def fake_run(cmd):
            # Simulate the compiler (or a concurrent edit) changing what a
            # naive post-hoc re-hash would see.
            vo.write_bytes(b"compiled")
            return _fake_completed(returncode=0)

        monkeypatch.setattr(cutoff_rocq.subprocess, "run", fake_run)
        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", False)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit) as exc_info:
            cutoff_rocq.main()
        assert exc_info.value.code == 0

        assert sha_mock.call_count == 1, "the source must be hashed exactly once"
        assert stamp.read_text() == "pre-compile-hash"


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
        stamp.write_text(hashlib.sha256(vfile.read_bytes()).hexdigest())

        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", False)
        run_mock = MagicMock(return_value=_fake_completed(returncode=0))
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit) as exc_info:
            cutoff_rocq.main()
        assert exc_info.value.code == 0

        # Exactly one subprocess call -- the real compile -- and no coqtop
        # `-require` check at all: the interactive gate must short-circuit
        # before the stamp is even consulted.
        run_mock.assert_called_once()
        cmd = run_mock.call_args[0][0]
        assert cmd[0] == cutoff_rocq.REAL_ROCQ
        assert cmd[1] == "compile"
        assert cutoff_rocq.COQTOP not in cmd


class TestInteractiveReuseAcceptance:
    """(d) with CUTOFF_AGENT_INTERACTIVE=1 set, a matching stamp triggers the
    cheap `coqtop -require` acceptance check instead of a real compile.
    """

    def test_matching_stamp_triggers_coqtop_check(self, tmp_path, monkeypatch):
        vfile = _write_source(tmp_path)
        vo = tmp_path / "Foo.vo"
        vo.write_bytes(b"up-to-date")
        glob = tmp_path / "Foo.glob"
        glob.write_bytes(b"")
        stamp = tmp_path / "Foo.vo.cutoff-stamp"
        real_hash = hashlib.sha256(vfile.read_bytes()).hexdigest()
        stamp.write_text(real_hash)

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

        # Bytes stay exactly as they were -- only mtimes may move.
        assert vo.read_bytes() == b"up-to-date"
        assert glob.read_bytes() == b""
        assert stamp.read_text() == real_hash

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
        real_hash = hashlib.sha256(vfile.read_bytes()).hexdigest()
        stamp.write_text(real_hash)

        monkeypatch.setattr(cutoff_rocq, "AGENT_INTERACTIVE", True)

        def fake_run(cmd, **kwargs):
            if cmd[0] == cutoff_rocq.COQTOP:
                return _fake_completed(returncode=1, stdout=b"Error: inconsistent assumptions\n")
            return _fake_completed(returncode=0)

        run_mock = MagicMock(side_effect=fake_run)
        monkeypatch.setattr(cutoff_rocq.subprocess, "run", run_mock)
        argv = ["compile", "-Q", str(tmp_path), "Lib", str(vfile)]
        monkeypatch.setattr(cutoff_rocq.sys, "argv", ["cutoff_rocq.py", *argv])

        with pytest.raises(SystemExit) as exc_info:
            cutoff_rocq.main()
        assert exc_info.value.code == 0

        assert run_mock.call_count == 2  # the coqtop check, then the real compile
        real_compile_calls = [c for c in run_mock.call_args_list if c.args[0][0] == cutoff_rocq.REAL_ROCQ]
        assert len(real_compile_calls) == 1
