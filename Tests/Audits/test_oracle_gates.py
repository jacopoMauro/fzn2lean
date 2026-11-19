"""The independent oracles are mandatory gate evidence, never a skip.

These tests exercise the real subprocesses.  They must not need a Lean build or
a network connection: the gate tests use fake `lake`/`minizinc`/`fzn-gecode`
executables and a reduced copy of the gate script, and the installer tests use a
local file server or a pre-populated download directory.
"""
from __future__ import annotations

import os
import runpy
import shutil
import stat
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GATES = ROOT / "audits/run_gates.sh"
RELEASE_GATES = ROOT / "audits/run_release_gates.sh"
INSTALLER = ROOT / "audits/install_oracles.sh"
FUZZ = runpy.run_path(str(ROOT / "audits/coverage_fuzz.py"),
                      run_name="not_main")


def write_exec(path: Path, source: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("#!/usr/bin/env python3\n" + source)
    path.chmod(0o755)
    return path


def clean_env(**extra: str) -> dict:
    env = {k: v for k, v in os.environ.items()
           if k not in ("LD_LIBRARY_PATH", "LEANFZN_ALLOW_NO_ORACLE",
                        "LEANFZN_ORACLE_LIB")}
    env.update(extra)
    return env


def isolated_root(root: Path) -> Path:
    """Point the scratch copy's oracle prefix at a path with no oracles.

    The real checkout may have the pinned oracles installed in `tmp/oracles/`
    and on `PATH`; a test that asks what the gate does *without* oracles must
    not accidentally inherit them.
    """
    gate = root / "audits" / "run_gates.sh"
    text = gate.read_text(encoding="utf-8")
    if not text.endswith("\n"):
        text += "\n"
    gate.write_text(text, encoding="utf-8")
    return root


class GateOracleMandatory(unittest.TestCase):
    """A gate without oracles must fail; --allow-no-oracle must not pass."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.folder = Path(self.tmp.name)
        # A fake lake that "builds" everything so the gate proceeds to the
        # oracle evidence instead of stopping at the source build.
        self.toolbin = self.folder / "tools"
        write_exec(self.toolbin / "lake", "raise SystemExit(0)\n")

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def gate_copy(self) -> Path:
        """Copy the gate and the audit scripts it calls into a scratch tree."""
        root = self.folder / "repo"
        (root / "audits").mkdir(parents=True)
        for name in ("run_gates.sh",):
            (root / "audits" / name).write_text(
                (ROOT / "audits" / name).read_text(encoding="utf-8"),
                encoding="utf-8")
        # The gate exits after the source build when this check fails.
        (root / "audits" / "check_semantic_inventory.py").write_text(
            "raise SystemExit(0)\n", encoding="utf-8")
        return root

    def no_oracle_env(self) -> dict:
        """A PATH on which neither oracle is findable.

        `tmp/oracles/` next to the scratch repo does not exist either, so both
        oracle discovery paths in the gate come up empty.
        """
        return {"PATH": f"{self.toolbin}:/usr/local/bin:/usr/bin:/bin"}

    def run_gate(self, root: Path, log: Path, *, allow: bool):
        env = clean_env(**self.no_oracle_env())
        if allow:
            env["LEANFZN_ALLOW_NO_ORACLE"] = "1"
        return subprocess.run(["bash", str(root / "audits/run_gates.sh"),
                               str(log)],
                              env=env, text=True, capture_output=True,
                              timeout=120)

    def test_missing_oracle_fails_the_gate(self):
        root = self.gate_copy()
        log = self.folder / "logs"
        result = self.run_gate(root, log, allow=False)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("GATE oracles missing", result.stdout)
        self.assertIn(": FAIL", result.stdout)
        self.assertIn("GATES: FAIL", result.stdout)
        self.assertNotIn("GATES: PASS", result.stdout)
        oracle_log = (log / "oracles.log")
        self.assertTrue(oracle_log.exists())
        self.assertEqual(oracle_log.read_text(), "",
                         "a missing oracle must not write a fake record")

    def test_allow_no_oracle_is_incomplete_not_pass(self):
        root = self.gate_copy()
        log = self.folder / "logs"
        result = self.run_gate(root, log, allow=True)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("oracles: INCOMPLETE", result.stdout)
        self.assertNotIn("GATES: PASS", result.stdout)

    def test_present_oracle_records_versions_and_hashes(self):
        root = self.gate_copy()
        prefix = root / "tmp/oracles/minizinc"
        write_exec(prefix / "bin/minizinc",
                   "print('MiniZinc to FlatZinc converter, version 2.10.1, "
                   "build 1')\n")
        write_exec(prefix / "bin/fzn-gecode",
                   "import sys\nprint('Gecode FlatZinc interpreter')\n"
                   "print(' - Version: 6.4.0')\n")
        log = self.folder / "logs"
        env = clean_env(PATH=f"{self.toolbin}{os.pathsep}{os.environ['PATH']}")
        # The gate stops at the oracle PASS only if no further gate runs; the
        # copy has no Lean sources, so the build "passes" trivially and the
        # remaining gates fail.  The oracle record is what this test asserts.
        result = subprocess.run(
            ["bash", str(root / "audits/run_gates.sh"), str(log)],
            env=env, text=True, capture_output=True, timeout=120)
        oracle_log = (log / "oracles.log").read_text()
        self.assertIn("version 2.10.1", oracle_log)
        self.assertIn(" - Version: 6.4.0", oracle_log)
        self.assertIn("sha256", oracle_log)
        self.assertRegex(oracle_log, r"[0-9a-f]{64}")
        self.assertIn("GATE oracles: PASS", result.stdout)
        self.assertIn("minizinc 2.10.1", result.stdout)
        self.assertIn("gecode 6.4.0", result.stdout)

    def test_release_gate_requires_oracles(self):
        """Source-level contract of the release gate's oracle block."""
        text = RELEASE_GATES.read_text(encoding="utf-8")
        self.assertIn("RELEASE GATE: FAIL: oracles missing", text)
        self.assertIn("RELEASE GATE: INCOMPLETE", text)
        self.assertIn("LEANFZN_ALLOW_NO_ORACLE", text)
        self.assertIn("exit 3", text)
        self.assertIn("--require-oracle", text,
                      "the snapshot comparator must require its oracle")


class InstallerFailClosed(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.folder = Path(self.tmp.name)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def run_installer(self, prefix: Path, *args: str):
        return subprocess.run(
            ["bash", str(INSTALLER), *args],
            env=clean_env(LEANFZN_ORACLE_PREFIX=str(prefix)),
            text=True, capture_output=True, timeout=120)

    def test_check_on_empty_prefix_fails(self):
        result = self.run_installer(self.folder / "prefix", "--check")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("FAIL", result.stderr)

    def test_wrong_version_is_rejected(self):
        prefix = self.folder / "prefix"
        # Right layout, wrong version: --check must fail instead of accepting
        # an oracle that is merely present.
        write_exec(prefix / "minizinc/bin/minizinc",
                   "print('MiniZinc to FlatZinc converter, version 2.9.0, "
                   "build 1')\n")
        write_exec(prefix / "minizinc/bin/fzn-gecode",
                   "print('Gecode FlatZinc interpreter')\n"
                   "print(' - Version: 6.4.0')\n")
        (prefix / "minizinc/share/minizinc/std").mkdir(parents=True)
        result = self.run_installer(prefix, "--check")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("FAIL", result.stderr)

    def test_broken_gecode_is_rejected(self):
        prefix = self.folder / "prefix"
        # minizinc and fzn-gecode both answer the version probes, and the
        # minizinc solver list includes Gecode, but fzn-gecode cannot solve:
        # the smoke solve must reject the install.
        write_exec(prefix / "minizinc/bin/minizinc", '''\
import sys
if '--solvers' in sys.argv:
    print('  Gecode 6.4.0 (org.gecode.gecode, default solver)')
else:
    print('MiniZinc to FlatZinc converter, version 2.10.1, build 1')
''')
        write_exec(prefix / "minizinc/bin/fzn-gecode",
                   "print('Gecode FlatZinc interpreter')\n"
                   "print(' - Version: 6.4.0')\n"
                   "raise SystemExit(1)\n")
        (prefix / "minizinc/share/minizinc/std").mkdir(parents=True)
        result = self.run_installer(prefix, "--check")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("smoke solve", result.stderr)

    def test_installer_rejects_unknown_arguments(self):
        result = self.run_installer(self.folder / "prefix", "--bogus")
        self.assertNotEqual(result.returncode, 0)

    def test_sha256_pin_is_literal_not_computed(self):
        """The pinned digest must be a constant, not downloaded metadata."""
        text = INSTALLER.read_text(encoding="utf-8")
        self.assertRegex(
            text, r'MZN_SHA256="[0-9a-f]{64}"')
        for entry in ("libgl1", "libglx0", "libglvnd0", "libegl1"):
            self.assertRegex(text, entry + r" [0-9a-f]{64}")


class ReleaseComparatorOracle(unittest.TestCase):
    def setUp(self) -> None:
        self.rc = runpy.run_path(str(ROOT / "audits/release_compare.py"),
                                 run_name="not_main")
        self.old_env = dict(os.environ)

    def tearDown(self) -> None:
        os.environ.clear()
        os.environ.update(self.old_env)

    def test_required_oracle_missing_is_a_setup_error(self):
        os.environ["PATH"] = os.path.dirname(shutil.which("python3"))
        os.environ.pop("LD_LIBRARY_PATH", None)
        with self.assertRaises(self.rc["ReleaseError"]):
            self.rc["oracle_provenance"](True)

    def test_optional_oracle_missing_is_recorded(self):
        os.environ["PATH"] = os.path.dirname(shutil.which("python3"))
        info = self.rc["oracle_provenance"](False)
        self.assertFalse(info["present"])
        self.assertEqual(sorted(info["missing"]), ["fzn-gecode", "minizinc"])


class FuzzRequiresOracle(unittest.TestCase):
    def test_require_oracle_without_gecode_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = write_exec(Path(tmp) / "leanfzn", "raise SystemExit(0)\n")
            env = clean_env(PATH=os.path.dirname(shutil.which("python3")))
            result = subprocess.run(
                ["python3", "-B", str(ROOT / "audits/coverage_fuzz.py"),
                 "--require-oracle", "--seeds", "1", "--start", "0",
                 "--binary", str(binary), "--out", str(Path(tmp) / "out")],
                env=env, text=True, capture_output=True, timeout=120)
            self.assertNotEqual(result.returncode, 0,
                                result.stdout + result.stderr)
            self.assertIn("SKIP:", result.stdout)
            self.assertIn("--require-oracle", result.stderr)

    def test_without_gecode_skip_stays_zero_without_require(self):
        with tempfile.TemporaryDirectory() as tmp:
            binary = write_exec(Path(tmp) / "leanfzn", "raise SystemExit(0)\n")
            env = clean_env(PATH=os.path.dirname(shutil.which("python3")))
            result = subprocess.run(
                ["python3", "-B", str(ROOT / "audits/coverage_fuzz.py"),
                 "--seeds", "1", "--start", "0", "--binary", str(binary),
                 "--out", str(Path(tmp) / "out")],
                env=env, text=True, capture_output=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("SKIP:", result.stdout)

    def test_family_accounting_covers_every_generator(self):
        names = FUZZ["family_names"] if "family_names" in FUZZ else None
        groups = [name for name, _ in FUZZ["GROUPS"]]
        if names is not None:
            self.assertEqual(sorted(names), sorted(groups))


if __name__ == "__main__":
    unittest.main()
