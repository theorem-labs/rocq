#!/usr/bin/env python3
"""Tests for the one-value-per-channel check (BET-84 P3).

The check exists because of a defect that a reviewer reintroduced by hand
and the first version of the check did not catch: an evaluator that digests
a value itself, beside a record site that digests it another way. Case (a)
is that defect, put back in the shape the reviewer used, and case (e) is the
same defect on a channel named by an identifier rather than a literal, which
is the half the first version could not see at all.

Run: python3 dev/tools/census/test_replay_channels.py
"""
from __future__ import annotations

import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
CHECK = HERE / "replay_channels.py"

CLEAN = '''
let recorded_thing key =
  match lookup key with
  | None -> None
  | Some v -> Some (Proof_recorder.digest ~what:"thing" v)

let () =
  Proof_replay.register_evaluator "thing" (fun key ->
      match recorded_thing key with
      | v -> Proof_replay.Value v
      | exception _ -> Proof_replay.Unknown)

let read_thing key =
  if Proof_recorder.active () then
    Proof_recorder.read ~row:"1" ~channel:"thing" ~key:(fun () -> key)
      ~value:(fun () -> recorded_thing key)
'''

#: The reviewer's defect: the evaluator computes the value itself.
EVALUATOR_DIGESTS = CLEAN.replace(
    '''      match recorded_thing key with
      | v -> Proof_replay.Value v
      | exception _ -> Proof_replay.Unknown)''',
    '''      match lookup key with
      | None -> Proof_replay.Value None
      | Some v -> Proof_replay.Value (Some (Proof_record.digest_value v)))''',
)

#: Two different value functions, one per side.
TWO_FUNCTIONS = CLEAN.replace(
    "match recorded_thing key with", "match recorded_other key with")

#: A channel named by an identifier, as the nametabs name theirs, with the
#: same defect. The first version of the check skipped these sites.
DYNAMIC_DEFECT = '''
let ch_thing = SI.summary_name ^ "/thing"

let recorded_lookup f =
  match f () with
  | v -> Some (Proof_recorder.digest ~what:SI.summary_name v)
  | exception Not_found -> None

let record ~channel ~id key value =
  Proof_recorder.read_by ~row:"6" ~channel ~id ~key ~value:(fun () -> recorded_lookup value)

let look key = record ~channel:ch_thing ~id:key (fun () -> key) (fun () -> Tab.find key)

let () =
  Proof_replay.register_evaluator ch_thing (fun key ->
      match Tab.find key with
      | v -> Proof_replay.Value (Some (Proof_record.digest_value v))
      | exception Not_found -> Proof_replay.Value None)
'''

#: The same, with both sides on the one function.
DYNAMIC_CLEAN = DYNAMIC_DEFECT.replace(
    '''      match Tab.find key with
      | v -> Proof_replay.Value (Some (Proof_record.digest_value v))
      | exception Not_found -> Proof_replay.Value None)''',
    '''      match recorded_lookup (fun () -> Tab.find key) with
      | v -> Proof_replay.Value v
      | exception _ -> Proof_replay.Unknown)''',
)


def run(check: pathlib.Path, source: str):
    root = pathlib.Path(tempfile.mkdtemp(prefix="replay-channels-"))
    try:
        (root / "kernel").mkdir()
        (root / "kernel" / "probe.ml").write_text(source)
        p = subprocess.run([sys.executable, str(check), "--root", str(root)],
                           capture_output=True, text=True)
        return p.returncode, p.stdout + p.stderr
    finally:
        shutil.rmtree(root, ignore_errors=True)


class OneValuePerChannel(unittest.TestCase):
    def test_clean_tree_passes(self):
        rc, out = run(CHECK, CLEAN)
        self.assertEqual(rc, 0, out)
        self.assertIn("single implementation", out)

    def test_evaluator_that_digests_is_caught(self):
        """The reviewer's reintroduced defect."""
        rc, out = run(CHECK, EVALUATOR_DIGESTS)
        self.assertEqual(rc, 1, out)
        self.assertIn("thing", out)

    def test_two_value_functions_are_caught(self):
        rc, out = run(CHECK, TWO_FUNCTIONS)
        self.assertEqual(rc, 1, out)
        self.assertIn("two implementations", out)

    def test_dynamic_channel_defect_is_caught(self):
        """A channel named by an identifier, not a literal."""
        rc, out = run(CHECK, DYNAMIC_DEFECT)
        self.assertEqual(rc, 1, out)
        self.assertIn("ch_thing", out)

    def test_dynamic_channel_clean_passes(self):
        rc, out = run(CHECK, DYNAMIC_CLEAN)
        self.assertEqual(rc, 0, out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
