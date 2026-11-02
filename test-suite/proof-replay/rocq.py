"""The Rocq under test, and how its programs are run (BET-84)."""

import os
import shutil
import subprocess
import time
from pathlib import Path


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


def last_line(res):
    text = (res["err"] or res["out"]).strip().splitlines()
    return text[-1][:300] if text else "(no output)"
