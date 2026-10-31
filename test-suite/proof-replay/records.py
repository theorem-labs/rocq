"""A fixture's proof records: the registration's records published, changed
as the fixture says, and one record file read (BET-84)."""

import hashlib
import json
import os
import shutil
from pathlib import Path

from objfile import segments
from trees import lib_name, record_src, vo_src


def opaques_span(data, what):
    """(position, length) of the `opaques` segment of a .vo's bytes."""
    seg = segments(data, what).get("opaques")
    if seg is None:
        raise ValueError("%s: no opaques segment" % what)
    return seg[0], seg[1]


def publish_records(spec, reg, records):
    """The registration's records, under the names -proof-replay-dir reads.

    Each record's `.vo` is published beside it under the same name, as a
    registration tree holds it: a record made with `-proof-record-vo-ref`
    refers to the opaque proofs of that object.  `vo_mutation` then removes
    those objects (`remove`), or changes one byte inside their opaque proofs
    (`change`), so a fixture can show what a referring proof does without
    the object it was registered with.
    """
    published = []
    objects = []
    for src in spec["files"]:
        rec = record_src(reg, src)
        if not rec.is_file():
            return None, "registration wrote no record for %s" % src
        if src in spec["unpublished"]:
            continue
        name = lib_name(spec, src)
        targets = []
        if spec["record_layout"] in ("dotted", "both"):
            targets.append(records / (name + ".proof-record.jsonl"))
        if spec["record_layout"] in ("slashed", "both"):
            targets.append(records / (name.replace(".", "/") + ".proof-record.jsonl"))
        for target in targets:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(rec, target)
            published.append(target)
            obj = Path(str(target)[:-len(".proof-record.jsonl")] + ".vo")
            shutil.copyfile(vo_src(reg, src), obj)
            objects.append(obj)
    mutation = spec.get("vo_mutation")
    for obj in objects:
        if mutation == "remove":
            obj.unlink()
            continue
        if mutation == "change":
            data = bytearray(obj.read_bytes())
            try:
                pos, length = opaques_span(bytes(data), obj.name)
            except ValueError as exc:
                return None, str(exc)
            data[pos + length // 2] ^= 0xFF
            obj.write_bytes(bytes(data))
        elif mutation is not None:
            return None, "unknown vo_mutation %r" % mutation
        os.chmod(obj, 0o444)
    # `record_patch` sets one recorded read's value before the digest is
    # taken, so a fixture can hold a record no registration of its tree would
    # write (a null read inside an open section, say) and still be bound.
    for patch in spec.get("record_patch", []):
        for path in published:
            lines = path.read_text().splitlines()
            hit = False
            for k, line in enumerate(lines):
                entry = json.loads(line)
                if entry.get("kind") == "proof" and entry.get("name") == patch["proof"]:
                    for read in entry.get("reads", []):
                        if read.get("channel") == patch["channel"] and read.get("key") == patch["key"]:
                            read["value"] = patch["value"]
                            hit = True
                    lines[k] = json.dumps(entry, separators=(",", ":"))
            if not hit:
                return None, "record_patch matched no read: %r" % (patch,)
            path.write_text("".join(l + "\n" for l in lines))
    # A record the compiling user can write is refused, and so is one with no
    # digest to check it against (P3Deep F1, P3Bugs): a registration publishes
    # its records read-only with their SHA-256 beside them, so the fixtures do.
    # With `-proof-replay-dir` and no digest option, the directories from the
    # records directory down to each record must be read-only too (reviewer
    # round 2 of e560ab16e4, X4): `open_dirs` gives the write bit back.
    for path in published:
        side = Path(str(path) + ".sha256")
        side.write_text(hashlib.sha256(path.read_bytes()).hexdigest() + "\n")
        os.chmod(side, 0o444)
        os.chmod(path, 0o444)
    for d, _, _ in os.walk(records):
        os.chmod(d, 0o555)
    return published, None


def parse_record(path):
    """The record file as (header, [proof...], trailer).  Raises ValueError."""
    header, proofs, trailer = None, [], None
    for n, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip():
            raise ValueError("%s:%d: empty line" % (path.name, n))
        obj = json.loads(line)
        kind = obj.get("kind")
        if kind == "header":
            if header is not None or proofs or trailer is not None:
                raise ValueError("%s:%d: a second header" % (path.name, n))
            header = obj
        elif kind == "proof":
            if header is None or trailer is not None:
                raise ValueError("%s:%d: a proof outside the file's body" % (path.name, n))
            proofs.append(obj)
        elif kind == "trailer":
            if trailer is not None:
                raise ValueError("%s:%d: a second trailer" % (path.name, n))
            trailer = obj
        else:
            raise ValueError("%s:%d: kind %r" % (path.name, n, kind))
    if header is None or trailer is None:
        raise ValueError("%s: no header or no trailer" % path.name)
    if trailer.get("proof_count") != len(proofs):
        raise ValueError("%s: proof_count %r against %d proof lines"
                         % (path.name, trailer.get("proof_count"), len(proofs)))
    return header, proofs, trailer
