#!/usr/bin/env python3
"""Drop-in replacement for `$(ROCQ)` ("rocq compile ARGS... FILE.v") in a
coq_makefile-generated Makefile. For files in the zygote manifest, talks to
a lazily-spawned per-group rocq-zygote daemon over a Unix socket; falls back
to an ordinary, unmodified `rocq compile` invocation for every other file,
and for ANY failure talking to a zygote (missing manifest entry, daemon
spawn failure, MISMATCH response, socket error).

Configuration via environment variables (all required except the last two):
  ROCQ_ZYGOTE_MANIFEST   path to zygote-manifest.json
  ROCQ_ZYGOTE_EXE        path to the rocq-zygote executable
  ROCQ_ZYGOTE_REAL_ROCQ  path to the real, stock `rocq` binary (fallback + fed to the daemon)
  ROCQ_ZYGOTE_SOCKDIR    directory for per-group sockets/locks (created if missing)
  ROCQLIB                passed through to both the daemon and the fallback
  ROCQ_ZYGOTE_COQLIBS    shared -Q/-R flags (same for every file in this tree)
  ROCQ_ZYGOTE_IDLE       idle timeout seconds for spawned daemons (default 600)
"""
import errno
import fcntl
import json
import os
import socket
import subprocess
import sys
import time

MANIFEST_PATH = os.environ["ROCQ_ZYGOTE_MANIFEST"]
ZYGOTE_EXE = os.environ["ROCQ_ZYGOTE_EXE"]
REAL_ROCQ = os.environ["ROCQ_ZYGOTE_REAL_ROCQ"]
SOCKDIR = os.environ["ROCQ_ZYGOTE_SOCKDIR"]
IDLE_TIMEOUT = os.environ.get("ROCQ_ZYGOTE_IDLE", "600")

_manifest = None


def manifest():
    global _manifest
    if _manifest is None:
        with open(MANIFEST_PATH) as f:
            _manifest = json.load(f)
    return _manifest


def real_rocq_compile(flags, file_v):
    return subprocess.run([REAL_ROCQ, "compile"] + flags + [file_v]).returncode


def ensure_zygote(group, prefix_file, sock_path):
    if os.path.exists(sock_path):
        try:
            s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            s.settimeout(2)
            s.connect(sock_path)
            s.close()
            return True
        except OSError:
            pass
    lock_path = os.path.join(SOCKDIR, f"{group}.lock")
    with open(lock_path, "w") as lockf:
        fcntl.flock(lockf, fcntl.LOCK_EX)
        try:
            # Re-check after acquiring the lock -- another process may have
            # already finished spawning while we waited.
            if os.path.exists(sock_path):
                try:
                    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                    s.settimeout(2)
                    s.connect(sock_path)
                    s.close()
                    return True
                except OSError:
                    pass
            log_path = os.path.join(SOCKDIR, f"{group}.log")
            coqlibs_raw = os.environ.get("ROCQ_ZYGOTE_COQLIBS", "")
            coqlibs = coqlibs_raw.split()
            with open(log_path, "ab") as log:
                subprocess.Popen(
                    [ZYGOTE_EXE, "-q"] + coqlibs + [
                        "--rocq-zygote-prefix", prefix_file,
                        "--rocq-zygote-socket", sock_path,
                        "--rocq-zygote-idle-timeout", IDLE_TIMEOUT,
                        "--rocq-zygote-coqlibs", coqlibs_raw,
                    ],
                    stdout=log, stderr=log, stdin=subprocess.DEVNULL,
                    start_new_session=True,
                )
            deadline = time.time() + 120
            while time.time() < deadline:
                if os.path.exists(sock_path):
                    try:
                        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                        s.settimeout(2)
                        s.connect(sock_path)
                        s.close()
                        return True
                    except OSError:
                        pass
                time.sleep(0.05)
            return False
        finally:
            fcntl.flock(lockf, fcntl.LOCK_UN)


def try_zygote(group, prefix_file, file_v, output_v, echo, tmp_base):
    sock_path = os.path.join(SOCKDIR, f"{group}.sock")
    if not ensure_zygote(group, prefix_file, sock_path):
        return None
    stdout_tmp = f"{tmp_base}.zygote.out.{os.getpid()}"
    stderr_tmp = f"{tmp_base}.zygote.err.{os.getpid()}"
    try:
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(600)
        s.connect(sock_path)
        cwd = os.getcwd()
        coqlibs_raw = os.environ.get("ROCQ_ZYGOTE_COQLIBS", "")
        # cwd+coqlibs let the daemon chdir to match the client's own cwd before
        # resolving file_v/output_v (relative, 20d/21) and verify its own -Q/-R
        # flags still match this client's, rather than assuming both forever.
        req = f"COMPILE\t{cwd}\t{coqlibs_raw}\t{file_v}\t{output_v}\t{1 if echo else 0}\t{stdout_tmp}\t{stderr_tmp}\n"
        s.sendall(req.encode("utf-8"))
        buf = b""
        while not buf.endswith(b"\n"):
            chunk = s.recv(4096)
            if not chunk:
                break
            buf += chunk
        s.close()
    except OSError:
        return None
    line = buf.decode("utf-8", "replace").strip()
    parts = line.split("\t")
    if parts and parts[0] == "EXIT" and len(parts) == 2:
        try:
            code = int(parts[1])
        except ValueError:
            return None
        for path, stream in ((stdout_tmp, sys.stdout), (stderr_tmp, sys.stderr)):
            if os.path.exists(path):
                with open(path, "r", errors="replace") as f:
                    stream.write(f.read())
                os.unlink(path)
        return code
    # MISMATCH or anything else: fall back.
    for path in (stdout_tmp, stderr_tmp):
        try:
            os.unlink(path)
        except OSError:
            pass
    return None


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "compile":
        argv = argv[1:]
    vfiles = [a for a in argv if a.endswith(".v")]
    if not vfiles:
        sys.exit(real_rocq_compile(argv, ""))
    file_v = vfiles[-1]
    flags = [a for a in argv if a != file_v]
    echo = "-verbose" in flags

    # Pass the file (and its derived default output) through to the zygote
    # EXACTLY as coq_makefile itself would give them to a normal `rocq
    # compile` invocation (relative, matching the daemon's own cwd) --
    # Rocq embeds the literal path string it was given in every stored
    # Loc.t in the compiled library, so an absolute path here would make
    # the .vo differ from a stock relative-path compile byte-for-byte.
    output_v = os.path.splitext(file_v)[0] + ".vo"
    tmp_base = os.path.abspath(file_v)

    info = manifest().get(file_v)
    if info is not None:
        code = try_zygote(info["group"], info["prefix_file"], file_v, output_v, echo, tmp_base)
        if code is not None:
            sys.exit(code)
    sys.exit(real_rocq_compile(flags, file_v))


if __name__ == "__main__":
    os.makedirs(SOCKDIR, exist_ok=True)
    main()
