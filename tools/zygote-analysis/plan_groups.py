#!/usr/bin/env python3
"""Select zygote groups (prefix-trie nodes) from prefix_stats.json and emit:
  - /tmp/rocq-perf-zygote/zygote-groups/<id>.v     -- the shared prefix, verbatim
  - /tmp/rocq-perf-zygote/zygote-manifest.json     -- file -> {group, depth} | null
"""
import json
import os
from collections import defaultdict

STATS = "/tmp/rocq-perf-zygote/prefix_stats.json"
OUTDIR = "/tmp/rocq-perf-zygote/zygote-groups"
MANIFEST = "/tmp/rocq-perf-zygote/zygote-manifest.json"
MIN_FILES = 5  # don't bother with a zygote for fewer than this many files


def leading_requires(sentences):
    out = []
    for s in sentences:
        st = s.lstrip()
        if st.startswith("From ") or st.startswith("Require "):
            out.append(s)
        else:
            break
    return out


def main():
    d = json.load(open(STATS))
    prefixes = {f: leading_requires(seq) for f, seq in d["prefixes_by_file"].items()}

    node_files = defaultdict(list)
    for f, seq in prefixes.items():
        for k in range(1, len(seq) + 1):
            node_files[tuple(seq[:k])].append(f)

    candidates = sorted(node_files.items(), key=lambda kv: -(len(kv[0]) * len(kv[1])))

    os.makedirs(OUTDIR, exist_ok=True)
    remaining = set(prefixes.keys())
    groups = []  # (id, seq, files)
    for seq, files in candidates:
        files_set = set(files) & remaining
        if len(files_set) >= MIN_FILES:
            gid = f"g{len(groups):03d}"
            groups.append((gid, seq, sorted(files_set)))
            remaining -= files_set

    manifest = {}
    for gid, seq, files in groups:
        path = os.path.join(OUTDIR, f"{gid}.v")
        with open(path, "w") as f:
            for s in seq:
                f.write(s)
                f.write("\n")
        for fl in files:
            manifest[fl] = {"group": gid, "depth": len(seq), "prefix_file": path}

    for fl in remaining:
        manifest[fl] = None

    with open(MANIFEST, "w") as f:
        json.dump(manifest, f, indent=1)

    n = len(prefixes)
    covered = n - len(remaining)
    print(f"# {len(groups)} groups, covering {covered}/{n} files ({100*covered/n:.1f}%)")
    print(f"# {len(remaining)} files uncovered (compiled directly, no zygote)")
    total_sentences_saved = sum(len(seq) * (len(files) - 1) for _, seq, files in groups)
    print(f"# total (sentence x extra-file) amortized units: {total_sentences_saved}")
    for gid, seq, files in sorted(groups, key=lambda g: -len(g[2]) * len(g[1]))[:10]:
        print(f"  {gid}: depth={len(seq)} files={len(files)}  last={seq[-1][:80]!r}")
    print(f"# wrote {MANIFEST} and {len(groups)} prefix files under {OUTDIR}")


if __name__ == "__main__":
    main()
