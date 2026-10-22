#!/usr/bin/env python3
"""Measure the Require-prefix structure of the real 368-file (696-.v) vendor
tree at /rocq/cutoff/fulltree-build, using rocq-zygote's own
--rocq-zygote-dump-sentences mode (Rocq's real grammar entry, so sentence
boundaries -- including comment/whitespace skipping -- are exactly what a
real compile sees, not a line-oriented guess).

Usage: run inside the tree root with the opam-fp switch active.
"""
import json
import os
import subprocess
import sys
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed

TREE = "/rocq/cutoff/fulltree-build"
ZYGOTE = "/tmp/rocq-perf-zygote/_build/default/topbin/zygote.exe"
MAX_SENTENCES = 60
COQLIBS = [
    "-Q", "AgentSubmission/Coturn", "RocqVerifyHarness.AgentSubmission.Coturn",
    "-Q", "TaskSpecification/Problems", "RocqVerifyHarness.TaskSpecification.Problems",
    "-Q", "ProcessOversight", "RocqVerifyHarness.ProcessOversight",
]


def list_vfiles():
    with open(os.path.join(TREE, "_CoqProject")) as f:
        lines = [l.strip() for l in f]
    return [l for l in lines if l.endswith(".v")]


def dump_sentences(relfile):
    cmd = [ZYGOTE, "-q"] + COQLIBS + [
        "--rocq-zygote-dump-sentences", str(MAX_SENTENCES), relfile,
    ]
    env = dict(os.environ)
    env["ROCQLIB"] = "/tmp/rocq-perf-zygote/_build/install/default/lib/coq"
    try:
        r = subprocess.run(cmd, cwd=TREE, capture_output=True, timeout=60, env=env)
    except subprocess.TimeoutExpired:
        return relfile, None, "timeout"
    if r.returncode != 0:
        return relfile, None, r.stderr.decode("utf-8", "replace")[:500]
    raw = r.stdout.decode("utf-8", "replace")
    sentences = raw.split("\x00")
    if sentences and sentences[-1] == "":
        sentences.pop()
    return relfile, sentences, None


def leading_requires(sentences):
    """The leading run of sentences that are Require commands (From ... Require
    or bare Require), stopping at the first sentence that is not."""
    out = []
    for s in sentences:
        stripped = s.lstrip()
        if stripped.startswith("From ") or stripped.startswith("Require "):
            out.append(s)
        else:
            break
    return out


def main():
    vfiles = list_vfiles()
    print(f"# files in _CoqProject: {len(vfiles)}", file=sys.stderr)

    results = {}
    errors = {}
    with ProcessPoolExecutor(max_workers=64) as ex:
        futs = {ex.submit(dump_sentences, f): f for f in vfiles}
        for i, fut in enumerate(as_completed(futs)):
            relfile, sentences, err = fut.result()
            if err is not None:
                errors[relfile] = err
            else:
                results[relfile] = sentences
            if (i + 1) % 100 == 0:
                print(f"  ...{i+1}/{len(vfiles)}", file=sys.stderr)

    print(f"# successfully parsed: {len(results)}", file=sys.stderr)
    print(f"# errors: {len(errors)}", file=sys.stderr)
    for f, e in list(errors.items())[:10]:
        print(f"  ERROR {f}: {e[:200]}", file=sys.stderr)

    prefixes = {f: leading_requires(s) for f, s in results.items()}
    lengths = Counter(len(p) for p in prefixes.values())
    print(f"# leading-Require-run length histogram: {dict(sorted(lengths.items()))}", file=sys.stderr)

    # Build a trie over the leading-Require sequences; a node is keyed by the
    # tuple of sentences from the root. Count files reaching each node.
    node_files = defaultdict(list)  # prefix tuple -> [files]
    for f, seq in prefixes.items():
        for k in range(1, len(seq) + 1):
            node_files[tuple(seq[:k])].append(f)

    # Distinct FULL leading-Require-run prefixes (whole run, not sub-prefix)
    full_prefix_counts = Counter(tuple(p) for p in prefixes.values())
    print(f"# distinct full leading-Require-run prefixes: {len(full_prefix_counts)}", file=sys.stderr)

    n = len(prefixes)
    top5_full = full_prefix_counts.most_common(5)
    top5_full_cover = sum(c for _, c in top5_full)
    print(f"# top-5 FULL-prefix coverage: {top5_full_cover}/{n} ({100*top5_full_cover/n:.1f}%)", file=sys.stderr)

    # Best single trie node (any depth >=1) by file count -- the useful unit
    # for "one zygote per common sub-prefix".
    best_nodes = sorted(node_files.items(), key=lambda kv: -len(kv[1]))
    print("# top 10 trie nodes (any depth) by file count:", file=sys.stderr)
    for seq, files in best_nodes[:10]:
        print(f"  depth={len(seq)} files={len(files)}  last_sentence={seq[-1][:90]!r}", file=sys.stderr)

    # Greedy set cover using trie nodes (deepest/most files first) to see how
    # many distinct zygotes would be needed and what fraction of files they'd
    # cover, vs. the "too diverse" bar (top 10 covering <50%).
    remaining = set(prefixes.keys())
    covering = []
    candidates = sorted(node_files.items(), key=lambda kv: -len(kv[1]))
    ci = 0
    while remaining and ci < len(candidates):
        seq, files = candidates[ci]
        files_set = set(files) & remaining
        if len(files_set) >= 2:
            covering.append((seq, len(files_set)))
            remaining -= files_set
        ci += 1
        if len(covering) >= 30:
            break
    covered = n - len(remaining)
    print(f"# greedy trie-node cover (>=2 files/group, up to 30 groups): "
          f"{len(covering)} groups covering {covered}/{n} ({100*covered/n:.1f}%), "
          f"{len(remaining)} singleton/uncovered files", file=sys.stderr)
    for seq, cnt in covering[:15]:
        print(f"  depth={len(seq)} files={cnt}  last_sentence={seq[-1][:90]!r}", file=sys.stderr)

    out = {
        "n_files_coqproject": len(vfiles),
        "n_parsed": len(results),
        "n_errors": len(errors),
        "errors": errors,
        "leading_require_run_length_histogram": dict(lengths),
        "n_distinct_full_prefixes": len(full_prefix_counts),
        "top5_full_prefixes": [
            {"count": c, "sentences": list(p)} for p, c in top5_full
        ],
        "top5_full_coverage_fraction": top5_full_cover / n if n else 0.0,
        "greedy_trie_cover": [
            {"depth": len(seq), "n_files": cnt, "sentences": list(seq)}
            for seq, cnt in covering
        ],
        "greedy_trie_cover_fraction": covered / n if n else 0.0,
        "prefixes_by_file": {f: p for f, p in prefixes.items()},
    }
    with open("/tmp/rocq-perf-zygote/prefix_stats.json", "w") as f:
        json.dump(out, f, indent=1)
    print("# wrote /tmp/rocq-perf-zygote/prefix_stats.json", file=sys.stderr)


if __name__ == "__main__":
    main()
