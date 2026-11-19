#!/usr/bin/env python3
"""Replay `expected.txt` against the pinned MiniZinc 2.10.1 oracle.

This is the Python twin of `run.sh`: it runs every recorded model, compares
the *evaluated* output with `expected.txt`, and thereby checks the G-series
semantic assumptions (G2 truncated `int_div`/`int_mod`, G4 `int_pow` corner
exponents, G5 lexicographic `set_le`/`set_lt`, G6 `*_nonshifted` element
variants) against the reference implementation.

Run (from the repository root, with the oracle on PATH):
    eval "$(bash audits/install_oracles.sh --print-env)"
    python3 -B -m unittest discover -s Tests/Upstream/assumptions -p 'test_*.py'

A missing `minizinc` skips the class (never a pass); a wrong oracle version is
a failure, because a different oracle is not the pinned one.  As in `run.sh`,
`LEANFZN_ORACLE_LIB=<prefix>/lib` is honoured for the bundle's Qt/GL runtime
without polluting this process's `LD_LIBRARY_PATH`.
"""
import os
import re
import shutil
import subprocess
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "expected.txt"
VERSION_MARKER = "version 2.10.1"

ENGINE = shutil.which("minizinc")


def oracle_env():
    """Environment for the oracle child (bundle runtime prepended)."""
    env = dict(os.environ)
    lib = env.get("LEANFZN_ORACLE_LIB", "")
    if lib:
        env["LD_LIBRARY_PATH"] = lib + (":" + env["LD_LIBRARY_PATH"]
                                        if env.get("LD_LIBRARY_PATH") else "")
    return env


def parse_manifest(path):
    """Parse `expected.txt` into {model: (want_stdout, want_stderr)}."""
    records = {}
    cur = None
    for line in path.read_text().splitlines():
        m = re.fullmatch(r"=== (.*\.mzn) ===", line)
        if m:
            cur = m.group(1)
            records[cur] = {"want": None, "want-stderr": None}
            continue
        if line == "--- end ---":
            cur = None
            continue
        if cur is None:
            continue
        if line.startswith("want: "):
            value = line[len("want: "):]
            records[cur]["want"] = "" if value == "(empty)" else value
        elif line.startswith("want-stderr: "):
            records[cur]["want-stderr"] = line[len("want-stderr: "):]
    return records


def normalise(stdout):
    """The manifest's stdout form: trailing newline dropped, lines joined by |."""
    text = stdout.replace("\r\n", "\n")
    if text.endswith("\n"):
        text = text[:-1]
    return text.replace("\n", "|")


@unittest.skipIf(ENGINE is None,
                 "minizinc not on PATH; install the pinned bundle to run the "
                 "upstream assumption checks")
class UpstreamAssumptions(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not MANIFEST.is_file():
            raise AssertionError(f"missing manifest {MANIFEST}")
        cls.records = parse_manifest(MANIFEST)
        if not cls.records:
            raise AssertionError("manifest lists no models")

    def test_oracle_version(self):
        out = subprocess.run([ENGINE, "--version"], stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, env=oracle_env(),
                             check=True).stdout.decode()
        self.assertIn(VERSION_MARKER, out.splitlines()[0],
                      f"expected the pinned MiniZinc 2.10.1, got: {out!r}")

    def test_every_model(self):
        for model, rec in sorted(self.records.items()):
            with self.subTest(model=model):
                self.assertIsNotNone(rec["want"], f"{model}: no want record")
                self.assertIsNotNone(rec["want-stderr"],
                                     f"{model}: no want-stderr record")
                p = subprocess.run([ENGINE, str(HERE / model)],
                                   stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, env=oracle_env())
                got = normalise(p.stdout.decode())
                self.assertEqual(got, rec["want"],
                                 f"{model}: evaluated output differs from the "
                                 f"recorded MiniZinc 2.10.1 value")
                err = p.stderr.decode()
                if rec["want-stderr"] == "none":
                    self.assertEqual(err, "", f"{model}: unexpected stderr")
                else:
                    self.assertIn(rec["want-stderr"], err,
                                  f"{model}: stderr lacks the recorded text")

    def test_no_unlisted_models(self):
        """Every committed model has a record (so none is silently un-run)."""
        models = {p.name for p in HERE.glob("*.mzn")}
        self.assertEqual(models, set(self.records),
                         "models and expected.txt records disagree")


if __name__ == "__main__":
    unittest.main()
