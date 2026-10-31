"""A fixture's trees: a side staged as a tree, and the names of the files that
a compile writes beside a source (BET-84)."""

import os
import shutil

from fixture_spec import FIXTURES


def open_dirs(path):
    """Give the write permission back to every directory under `path`, the
    record directories `publish_records` made read-only included."""
    for d, _, _ in os.walk(path):
        os.chmod(d, 0o755)


def remove_tree(path):
    """`shutil.rmtree`, which cannot empty a read-only directory."""
    open_dirs(path)
    shutil.rmtree(path)


def copy_tree(src, dst):
    if dst.exists():
        shutil.rmtree(dst)
    shutil.copytree(src, dst)


def stage_tree(spec, side, dst):
    """The fixture's `side` tree (`original` or `edited`) at `dst`, with what
    `tree_dirs` and `tree_files` add to that side: an empty directory at each
    path (the way the grading engine blocks micromega's certificate caches),
    and a file of the fixture's directory copied to each path (a cache file
    no compile of the tree writes)."""
    copy_tree(FIXTURES / spec["name"] / side, dst)
    for rel in spec["tree_dirs"].get(side, []):
        (dst / rel).mkdir(parents=True)
    for rel, name in spec["tree_files"].get(side, {}).items():
        target = dst / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(FIXTURES / spec["name"] / name, target)


def lib_name(spec, src):
    return spec["root"] + "." + src[:-2].replace("/", ".")


def record_src(tree, src):
    return tree / (src[:-2] + ".proof-record.jsonl")


def summary_src(tree, src):
    return tree / (src[:-2] + ".proof-replay.json")


def vo_src(tree, src):
    return tree / (src[:-2] + ".vo")
