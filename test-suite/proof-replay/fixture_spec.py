"""A fixture's spec: its `expect.json`, checked and merged with the defaults
(BET-84).  README.md, "expect.json", gives the meaning of each key.
"""

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURES = HERE / "fixtures"

#: Every key `expect.json` may set, with its default.  `files` has none: a
#: fixture must set it.
DEFAULTS = {
    "doc": "",
    # A comment for the reader, like `doc`; the runner does not print it.
    "note": "",
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
    "usage": None,
    "mixed": None,
    "alt_register_flags": None,
    "vo_mutation": None,
    "record_patch": [],
    "record_trailers": {},
    "trigger_optional": None,
    "tree_files": {},
    "tree_dirs": {},
}
REQUIRED = ("files",)
SIDES = ("original", "edited")


def fixture_names():
    return sorted(p.name for p in FIXTURES.iterdir() if (p / "expect.json").is_file())


def spec_of(name, raw, where):
    """The spec of the fixture `name`, from its `expect.json` object `raw`;
    `where` is the fixture's directory.

    Every key has a default, so a misspelled key would take no effect and
    the fixture would test another tree than its author wrote.  Thus a key
    that `DEFAULTS` does not declare is an error, and so is a staging or
    publishing control that names a side, a file or a source the fixture
    does not have.  The ValueError names every problem.
    """
    if not isinstance(raw, dict):
        raise ValueError("fixtures/%s/expect.json: not a JSON object" % name)
    problems = []
    unknown = sorted(set(raw) - set(DEFAULTS) - set(REQUIRED))
    if unknown:
        problems.append("unknown key %s" % ", ".join(map(repr, unknown)))
    spec = dict(DEFAULTS)
    spec.update(raw)
    spec["name"] = name
    files = spec.get("files")
    if not isinstance(files, list) or not files:
        problems.append("`files` must be a non-empty list of the .v files")
        files = []
    if not isinstance(spec["unpublished"], list):
        problems.append("`unpublished` must be a list of files")
    else:
        stray = [src for src in spec["unpublished"] if src not in files]
        if stray:
            problems.append("`unpublished` names %s, which `files` does not list" % ", ".join(map(repr, stray)))
    for key, kind in (("tree_dirs", list), ("tree_files", dict)):
        if not isinstance(spec[key], dict):
            problems.append("`%s` must map a side to its paths" % key)
            continue
        for side, paths in spec[key].items():
            if side not in SIDES:
                problems.append("`%s` side %r is not %s" % (key, side, " or ".join(SIDES)))
            if not isinstance(paths, kind):
                problems.append("`%s` side %r must be a JSON %s" % (key, side, "list" if kind is list else "object"))
            elif kind is dict:
                for rel, src in paths.items():
                    if not (isinstance(src, str) and (where / src).is_file()):
                        problems.append("`tree_files` copies %r to %r, and the fixture has no such file" % (src, rel))
    if problems:
        raise ValueError("fixtures/%s/expect.json: %s" % (name, "; ".join(problems)))
    return spec


def load_spec(name):
    where = FIXTURES / name
    return spec_of(name, json.loads((where / "expect.json").read_text()), where)
