"""Fail-closed tests for the PGO/non-PGO release gate (PLAN C2.7/C3.4).

Every test asserts the process exit status of a real subprocess, not only a
printed summary.  Fake binaries and tiny models keep the suite independent of a
Lean build while still exercising the real comparator and manifest code.
"""
from __future__ import annotations

import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FIXED_K = ROOT / "audits/fixed_k.py"
RELEASE_COMPARE = ROOT / "audits/release_compare.py"

HEADER = ("case_id\tmodel\tmode\texpected_class\tknown_answer\t"
          "exact_counters\tknown_answer_source")

LAKE_PGO = """name = "fake"
version = "0.1.0"
moreLeancArgs = ["-fprofile-use=pgo/default.profdata", "-Wno-profile-instr-unprofiled"]

[[lean_lib]]
name = "LeanFzn"
globs = ["LeanFzn"]
"""


def stats(decisions: int = 2, conflicts: int = 0, complete: int = 1,
          gave_up: int = 0, incumbents: int = 0) -> str:
    return (
        "leanfzn: stats: steps=- "
        f"decisions={decisions} maxLevel=2 conflicts={conflicts} learned=0 "
        "learnedLitsBefore=0 learnedLitsAfter=0 learnedUnits=0 reductions=0 "
        "reducedClauses=0 reasonsTrimmed=0 propagations=1 rounds=0 "
        f"incumbents={incumbents} restarts=- complete={complete} "
        f"gaveUp={gave_up}")


SOLVER_SCRIPT = r'''#!/usr/bin/env python3
import json
import os
import sys
import time
from pathlib import Path

SPEC = json.loads(__SPEC__)
args = sys.argv[1:]
if args and args[0] == "check":
    print(SPEC.get("check_stdout", "solution accepted"))
    sys.exit(int(SPEC.get("check_rc", 0)))
if not args or args[0] != "solve":
    sys.exit(2)
model = Path(args[1]).name
case = SPEC.get(model)
if case is None:
    case = SPEC.get("default")
if case is None:
    print(f"fake solver: no spec for {model}", file=sys.stderr)
    sys.exit(2)
if case.get("sleep"):
    time.sleep(float(case["sleep"]))
out = case.get("stdout", "")
stats_line = case.get("stats", "")
if case.get("state"):
    p = Path(case["state"])
    n = int(p.read_text()) if p.exists() else 0
    p.write_text(str(n + 1))
    value = str(int(case.get("decisions", 2)) + n)
    out = out.replace("DECISIONS", value)
    stats_line = stats_line.replace("DECISIONS", value)
sys.stdout.write(out)
if out and not out.endswith("\n"):
    sys.stdout.write("\n")
if case.get("stats") == "missing":
    pass
elif case.get("stats") == "malformed":
    print("leanfzn: stats: steps=- decisions=? maxLevel=2", file=sys.stderr)
elif stats_line:
    print(stats_line, file=sys.stderr)
sys.stdout.flush()
sys.stderr.flush()
sys.exit(int(case.get("rc", 0)))
'''

TOOLCHAIN_SCRIPT = r'''#!/usr/bin/env python3
import sys
args = sys.argv[1:]
if args == ["--version"]:
    print("Lake version 5.0.0 (Lean version 4.35.0)")
elif args == ["env", "lean", "--version"]:
    print("Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit deadbeef, Release)")
elif args == ["env", "clang", "--version"]:
    print("clang version 23.1.0 (fake)")
    print("Target: x86_64-unknown-linux-gnu")
else:
    sys.exit(2)
'''


class ReleaseGates(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.base = Path(self._tmp.name)
        self.bin = self.base / "bin"
        self.bin.mkdir()
        self.models = self.base / "models"
        self.models.mkdir()

    def tearDown(self) -> None:
        self._tmp.cleanup()

    # ------------------------------------------------------------- helpers
    def executable(self, path: Path, text: str) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        path.chmod(path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP |
                   stat.S_IXOTH)
        return path

    def model(self, name: str, text: str) -> Path:
        path = self.models / name
        path.write_text(text, encoding="utf-8")
        return path

    def cohort(self, rows: list[str], name: str = "cohort.tsv",
               limit: int = 10) -> Path:
        path = self.base / name
        path.write_text(f"# conflict_limit: {limit}\n{HEADER}\n" +
                        "\n".join(rows) + "\n", encoding="utf-8")
        return path

    def solver(self, name: str, spec: dict, marker: str | None = None) -> Path:
        text = SOLVER_SCRIPT.replace("__SPEC__", repr(json.dumps(spec)))
        if marker:
            text = text + f"# fixture-variant: {marker}\n"
        return self.executable(self.bin / name, text)

    def run_fixed(self, cohort: Path, binary_a: Path | str,
                  binary_b: Path | str | None = None, cap: int = 5,
                  out: str = "fixed-out") -> subprocess.CompletedProcess:
        cmd = [
            sys.executable, "-B", str(FIXED_K),
            "--cohort-tsv", str(cohort), "--limit", "10",
            "--binary-a", str(binary_a),
            "--binary-b", str(binary_b if binary_b is not None else binary_a),
            "--out", str(self.base / out),
            "--json", str(self.base / out / "fixed_k.json"),
            "--root", str(self.base),
            "--lock", str(self.base / "measure.lock"),
            "--no-taskset",
            "--cap", str(cap),
        ]
        return subprocess.run(cmd, text=True, capture_output=True, timeout=60)

    def sat_model(self) -> Path:
        return self.model("sat_case.fzn",
                          "var 0..1: x :: output_var;\nsolve satisfy;\n")

    def opt_model(self) -> Path:
        return self.model("opt_case.fzn",
                          "var 0..1: z :: output_var;\nsolve maximize z;\n")

    def sat_spec(self, **kwargs) -> dict:
        spec = {
            "sat_case.fzn": {
                "stdout": "x = 1 ;\n----------\n",
                "stats": stats(),
                "rc": 0,
            },
            "check_stdout": "solution accepted",
            "check_rc": 0,
        }
        spec.update(kwargs)
        return spec

    def four_case_material(self) -> tuple[dict, Path]:
        """Tiny cohort covering sat/unsat/optimal/incomplete and all modes."""
        self.sat_model()
        self.model("conflict_case.fzn", "solve satisfy;\n")
        self.opt_model()
        self.model("inc_case.fzn",
                   "var 0..2: z :: output_var;\nsolve minimize z;\n")
        rows = [
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness",
            "unsat\tmodels/conflict_case.fzn\tsatisfy\tunsat\t-\ttrue\texhaustive",
            "opt\tmodels/opt_case.fzn\tmaximize\toptimal\t1\ttrue\tindependent",
            "inc\tmodels/inc_case.fzn\tminimize\tincomplete\t-\ttrue\tnone",
        ]
        cohort = self.cohort(rows, name="four.tsv")
        spec = {
            "sat_case.fzn": {
                "stdout": "x = 1 ;\n----------\n",
                "stats": stats(), "rc": 0,
            },
            "conflict_case.fzn": {
                "stdout": "=====UNSATISFIABLE=====\n",
                "stats": stats(decisions=1, conflicts=2), "rc": 1,
            },
            "opt_case.fzn": {
                "stdout": "z = 1 ;\n----------\n==========\n",
                "stats": stats(decisions=2, incumbents=1), "rc": 0,
            },
            "inc_case.fzn": {
                "stdout": "z = 2 ;\n----------\n",
                "stats": stats(decisions=3, conflicts=10, complete=0,
                               gave_up=1, incumbents=1), "rc": 4,
            },
            "check_stdout": "solution accepted",
            "check_rc": 0,
        }
        return spec, cohort

    def snapshots(self, cohort: Path, spec: dict,
                  toolchain_nopgo: str | None = None,
                  extra_nopgo: str | None = None) -> tuple[Path, Path]:
        pgo = self.base / "snap/pgo"
        nopgo = self.base / "snap/nopgo"
        for variant, dest in (("pgo", pgo), ("nopgo", nopgo)):
            (dest / "LeanFzn").mkdir(parents=True)
            (dest / "pgo").mkdir()
            (dest / "audits").mkdir()
            (dest / "minizinc-wrapper").mkdir()
            (dest / "models").mkdir()
            lake = LAKE_PGO if variant == "pgo" else LAKE_PGO.replace(
                'moreLeancArgs = ["-fprofile-use=pgo/default.profdata", '
                '"-Wno-profile-instr-unprofiled"]\n', "")
            if variant == "nopgo" and extra_nopgo:
                lake += extra_nopgo
            (dest / "lakefile.toml").write_text(lake, encoding="utf-8")
            (dest / "lean-toolchain").write_text(
                toolchain_nopgo if variant == "nopgo" and toolchain_nopgo
                else "leanprover/lean4:v4.35.0\n", encoding="utf-8")
            (dest / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
            (dest / "pgo/default.profdata").write_text("PROFILE\n",
                                                       encoding="utf-8")
            (dest / "minizinc-wrapper/Dockerfile").write_text(
                "ARG MZN_VERSION=2.10.1\nARG MZN_SHA256=abc123\n",
                encoding="utf-8")
            (dest / "LeanFzn/Fake.lean").write_text("-- fake\n",
                                                    encoding="utf-8")
            shutil.copy2(cohort, dest / "audits/release_cohort.tsv")
            # The real gate snapshot contains the harness it executes; every
            # test snapshot does too so --require-snapshot-harness can be
            # exercised against the actual bytes.
            for harness in ("release_compare.py", "fixed_k.py"):
                shutil.copy2(ROOT / "audits" / harness,
                             dest / "audits" / harness)
            for model in self.models.iterdir():
                shutil.copy2(model, dest / "models" / model.name)
        pgo_bin = self.solver("pgo", spec, marker="pgo")
        nopgo_bin = self.solver("nopgo", spec, marker="nopgo")
        return pgo_bin, nopgo_bin

    def report_writer(self, name: str, report: dict, rc: int = 0) -> Path:
        """A fixed-k stand-in that writes ``report`` to its --json path."""
        report_file = self.base / f"{name}-report.json"
        report_file.write_text(json.dumps(report), encoding="utf-8")
        text = (
            "#!/usr/bin/env python3\n"
            "import json\n"
            "import sys\n"
            "from pathlib import Path\n"
            f"report = json.loads(Path({str(report_file)!r}).read_text())\n"
            "args = sys.argv[1:]\n"
            "out = None\n"
            "for i, arg in enumerate(args):\n"
            "    if arg == '--json':\n"
            "        out = Path(args[i + 1])\n"
            "if out is None:\n"
            "    sys.exit(2)\n"
            "out.parent.mkdir(parents=True, exist_ok=True)\n"
            "out.write_text(json.dumps(report), encoding='utf-8')\n"
            f"sys.exit({rc})\n"
        )
        return self.executable(self.bin / name, text)

    def successful_release(self) -> tuple[dict, Path, Path, Path, dict]:
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads(
            (self.base / "release-out/fixed_k/fixed_k.json").read_text())
        return spec, cohort, pgo, nopgo, report

    def run_release(self, cohort: Path, pgo_bin: Path, nopgo_bin: Path,
                    snapshot_pgo: Path | None = None,
                    snapshot_nopgo: Path | None = None,
                    out: str = "release-out",
                    extra: list[str] | None = None,
                    env: dict | None = None,
                    comparator: Path | None = None,
                    fixed_k: Path | str | None = None,
                    fixed_k_timeout: int = 60,
                    require_snapshot_harness: bool = False,
                    git_root: Path | None = None) -> subprocess.CompletedProcess:
        toolbin = self.base / "toolbin"
        self.executable(toolbin / "lake", TOOLCHAIN_SCRIPT)
        cmd = [
            sys.executable, "-B", str(comparator or RELEASE_COMPARE),
            "--pgo-binary", str(pgo_bin),
            "--nopgo-binary", str(nopgo_bin),
            "--snapshot-pgo", str(snapshot_pgo or self.base / "snap/pgo"),
            "--snapshot-nopgo", str(snapshot_nopgo or self.base / "snap/nopgo"),
            "--cohort", str(cohort),
            "--out", str(self.base / out),
            "--fixed-k", str(fixed_k or FIXED_K),
            "--measure-lock", str(self.base / "release.lock"),
            "--cap", "5",
            "--fixed-k-timeout", str(fixed_k_timeout),
            "--quiet",
        ]
        if require_snapshot_harness:
            cmd.append("--require-snapshot-harness")
        if git_root is not None:
            cmd.extend(["--git-root", str(git_root)])
        if extra:
            cmd.extend(extra)
        run_env = {**os.environ, **(env or {})}
        run_env["PATH"] = str(toolbin) + os.pathsep + run_env.get("PATH", "")
        return subprocess.run(cmd, text=True, capture_output=True, timeout=120,
                              env=run_env)

    # ------------------------------------------------- fixed_k failure paths
    def test_missing_stats_fails_closed(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        binary = self.solver("solver", self.sat_spec())
        spec = self.sat_spec()
        spec["sat_case.fzn"].pop("stats")
        binary = self.solver("solver", spec)
        result = self.run_fixed(cohort, binary)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("missing_stats", result.stdout + result.stderr)

    def test_malformed_stats_fails_closed(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        spec = self.sat_spec()
        spec["sat_case.fzn"]["stats"] = "malformed"
        binary = self.solver("solver", spec)
        result = self.run_fixed(cohort, binary)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("malformed_stats", result.stdout + result.stderr)

    def test_equal_missing_stats_are_not_a_pass(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        spec = self.sat_spec()
        spec["sat_case.fzn"].pop("stats")
        binary = self.solver("solver", spec)
        result = self.run_fixed(cohort, binary, binary)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("missing_stats", result.stdout + result.stderr)

    def test_malformed_stats_trailing_junk_fails_closed(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        spec = self.sat_spec()
        spec["sat_case.fzn"]["stats"] = stats() + " trailing-garbage"
        binary = self.solver("solver", spec)
        result = self.run_fixed(cohort, binary)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("malformed_stats", result.stdout + result.stderr)

    def test_seed_counter_mismatch_fails_closed(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        spec_a = self.sat_spec()
        spec_a["sat_case.fzn"]["stats"] = stats() + " seeds=1"
        spec_b = self.sat_spec()
        spec_b["sat_case.fzn"]["stats"] = stats() + " seeds=2"
        binary_a = self.solver("solver-a", spec_a)
        binary_b = self.solver("solver-b", spec_b)
        result = self.run_fixed(cohort, binary_a, binary_b)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("counter_mismatch", result.stdout + result.stderr)

    def test_fixed_k_tsv_keeps_historical_header_prefix(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        binary = self.solver("solver", self.sat_spec())
        result = self.run_fixed(cohort, binary)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        header = (self.base / "fixed-out/fixed_k.tsv").read_text().splitlines()[0]
        self.assertEqual(
            header.split("\t")[:12],
            ["case", "outcome_a", "outcome_b", "wall_a", "wall_b",
             "ratio_b_over_a", "counters_equal", "differing", "objective_a",
             "objective_b", "solutions_a", "solutions_b"])

    def test_missing_fixture_fails_closed(self):
        cohort = self.cohort([
            "sat\tmodels/absent.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        binary = self.solver("solver", self.sat_spec())
        result = self.run_fixed(cohort, binary)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("missing fixture", result.stdout + result.stderr)

    def test_unreadable_binary_fails_closed(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        binary = self.base / "not-executable"
        binary.write_text("not a binary\n", encoding="utf-8")
        binary.chmod(0o644)
        result = self.run_fixed(cohort, binary)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("not executable", result.stdout + result.stderr)

    def test_empty_cohort_fails_closed(self):
        self.sat_model()
        cohort = self.base / "empty.tsv"
        cohort.write_text(f"# conflict_limit: 10\n{HEADER}\n",
                          encoding="utf-8")
        binary = self.solver("solver", self.sat_spec())
        result = self.run_fixed(cohort, binary)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("no data rows", result.stdout + result.stderr)

    def test_timeout_fails_closed(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        spec = self.sat_spec()
        spec["sat_case.fzn"]["sleep"] = 30
        binary = self.solver("solver", spec)
        result = self.run_fixed(cohort, binary, cap=1)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("timeout", result.stdout + result.stderr)
        report = json.loads((self.base / "fixed-out/fixed_k.json").read_text())
        case = report["cases"][0]
        for side in ("a", "b"):
            self.assertTrue(case[side]["timed_out"])
            self.assertEqual(case[side]["outcome"], "timeout")
        self.assertIn("timeout", {failure["class"] for failure in case["failures"]})

    def test_two_equal_timeouts_are_not_a_pass(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        spec = self.sat_spec()
        spec["sat_case.fzn"]["sleep"] = 30
        binary = self.solver("solver", spec)
        result = self.run_fixed(cohort, binary, binary, cap=1)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("timeout", result.stdout + result.stderr)

    def test_wrong_objective_fails_closed(self):
        self.opt_model()
        cohort = self.cohort([
            "opt\tmodels/opt_case.fzn\tmaximize\toptimal\t1\ttrue\tindependent"])
        spec = {
            "opt_case.fzn": {
                "stdout": "z = 999 ;\n----------\n==========\n",
                "stats": stats(incumbents=1), "rc": 0,
            },
            "check_stdout": "solution accepted", "check_rc": 0,
        }
        binary = self.solver("solver", spec)
        result = self.run_fixed(cohort, binary)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("wrong_objective", result.stdout + result.stderr)

    def test_rejected_witness_fails_closed(self):
        self.sat_model()
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\ttrue\twitness"])
        spec = self.sat_spec()
        spec["check_rc"] = 1
        spec["check_stdout"] = "solution rejected: unsatisfied condition"
        binary = self.solver("solver", spec)
        result = self.run_fixed(cohort, binary)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("rejected_witness", result.stdout + result.stderr)

    def test_same_binary_identity_requires_exact_counters(self):
        self.sat_model()
        state = self.base / "counter-state"
        cohort = self.cohort([
            "sat\tmodels/sat_case.fzn\tsatisfy\tsat\t-\tfalse\twitness"])
        spec = self.sat_spec()
        spec["sat_case.fzn"]["state"] = str(state)
        spec["sat_case.fzn"]["stdout"] = (
            "x = 1 ;\n----------\n")
        # Replace the fixed counter with the state-dependent placeholder.
        spec["sat_case.fzn"]["stats"] = stats(decisions=0)
        # The script uses DECISIONS only when state is present; keep a marker
        # in the stats text so two runs differ.
        spec["sat_case.fzn"]["stats"] = (
            "leanfzn: stats: steps=- decisions=DECISIONS maxLevel=2 "
            "conflicts=0 learned=0 learnedLitsBefore=0 learnedLitsAfter=0 "
            "learnedUnits=0 reductions=0 reducedClauses=0 reasonsTrimmed=0 "
            "propagations=1 rounds=0 incumbents=0 restarts=- complete=1 "
            "gaveUp=0")
        binary = self.solver("solver", spec)
        result = self.run_fixed(cohort, binary, binary)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("counter_mismatch", result.stdout + result.stderr)

    # ----------------------------------------------- release_compare paths
    def test_release_compare_passes_clean_cohort(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        comparison = json.loads(
            (self.base / "release-out/comparison.json").read_text())
        self.assertEqual(comparison["status"], "pass")
        self.assertGreater(comparison["oracles"]["witness_checks"], 0)
        manifest = json.loads(
            (self.base / "release-out/manifest.json").read_text())
        self.assertEqual(manifest["compatibility"]["ok"], True)
        self.assertIn("moreLeancArgs",
                      manifest["compatibility"]["lakefile_one_line_diff"])
        self.assertNotEqual(
            manifest["variants"]["pgo"]["binary"]["sha256"],
            manifest["variants"]["nopgo"]["binary"]["sha256"])
        self.assertIn("RELEASE GATE: PASS",
                      (self.base / "release-out/summary.txt").read_text())

    def test_release_compare_stale_fixed_k_report_fails_closed(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        first = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        # A fixed-k stand-in that exits 0 without writing a report must not be
        # allowed to inherit the previous run's report from the same OUT.
        fake = self.executable(self.base / "toolbin" / "fake-fixed-k",
                               "#!/usr/bin/env python3\n")
        result = self.run_release(cohort, pgo, nopgo,
                                  extra=["--fixed-k", str(fake)])
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("did not write", result.stdout + result.stderr)

    def test_release_compare_limit_override_is_explicit(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        result = self.run_release(
            cohort, pgo, nopgo,
            extra=["--limit", "11", "--allow-limit-override"])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        manifest = json.loads(
            (self.base / "release-out/manifest.json").read_text())
        self.assertEqual(manifest["cohort"]["limit"], 11)
        self.assertEqual(manifest["cohort"]["frozen_limit"], 10)
        self.assertEqual(manifest["cohort"]["limit_override"], True)

    def test_release_compare_limit_override_without_flag_fails_closed(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        result = self.run_release(cohort, pgo, nopgo,
                                  extra=["--limit", "11"])
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("refusing override", result.stdout + result.stderr)
        comparison = json.loads(
            (self.base / "release-out/comparison.json").read_text())
        self.assertEqual(comparison["status"], "fail")
        self.assertEqual(comparison["failures"][0]["class"], "setup_error")

    def test_release_compare_fixed_k_timeout_fails_closed(self):
        spec, cohort = self.four_case_material()
        spec["sat_case.fzn"]["sleep"] = 30
        pgo, nopgo = self.snapshots(cohort, spec)
        result = self.run_release(cohort, pgo, nopgo, fixed_k_timeout=1)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("gate_timeout", result.stdout + result.stderr)
        comparison = json.loads(
            (self.base / "release-out/comparison.json").read_text())
        self.assertTrue(comparison["fixed_k"]["timed_out"])

    def test_release_compare_child_exit_1_with_report_is_failure(self):
        spec, cohort, pgo, nopgo, report = self.successful_release()
        fake = self.report_writer("fixed-k-exit1", report, rc=1)
        result = self.run_release(cohort, pgo, nopgo, out="release-out-2",
                                  fixed_k=fake)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("fixed_k_failed", result.stdout + result.stderr)

    def test_release_compare_report_model_hash_mismatch_fails_closed(self):
        spec, cohort, pgo, nopgo, report = self.successful_release()
        report["cases"][0]["model_sha256"] = "0" * 64
        fake = self.report_writer("fixed-k-model-hash", report)
        result = self.run_release(cohort, pgo, nopgo, out="release-out-2",
                                  fixed_k=fake)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("model_sha256", result.stdout + result.stderr)

    def test_release_compare_expected_manifest_matches(self):
        spec, cohort, pgo, nopgo, _ = self.successful_release()
        expected = self.base / "release-out/manifest.json"
        result = self.run_release(
            cohort, pgo, nopgo, out="release-out-2",
            extra=["--expected-manifest", str(expected)])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_release_compare_expected_manifest_setup_errors(self):
        spec, cohort, pgo, nopgo, _ = self.successful_release()
        cases = {
            "malformed": b"{not json",
            "invalid-utf8": b"\xff\xfe\x00{",
            "empty": b"{}",
            "nonobject": b"[]",
        }
        for label, data in cases.items():
            path = self.base / f"expected-{label}.json"
            path.write_bytes(data)
            with self.subTest(label=label):
                result = self.run_release(
                    cohort, pgo, nopgo, out=f"expected-{label}",
                    extra=["--expected-manifest", str(path)])
                self.assertEqual(result.returncode, 2,
                                 result.stdout + result.stderr)
                self.assertIn("expected manifest",
                              result.stdout + result.stderr)

    def test_release_compare_expected_manifest_tooling_pin_mismatch(self):
        spec, cohort, pgo, nopgo, _ = self.successful_release()
        manifest_path = self.base / "release-out/manifest.json"
        expected = json.loads(manifest_path.read_text())
        expected["tooling"]["fixed_k"]["sha256"] = "0" * 64
        tampered = self.base / "expected-tooling.json"
        tampered.write_text(json.dumps(expected), encoding="utf-8")
        result = self.run_release(
            cohort, pgo, nopgo, out="release-out-2",
            extra=["--expected-manifest", str(tampered)])
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("tooling.fixed_k.sha256",
                      result.stdout + result.stderr)

    def test_release_compare_snapshot_harness_pin_accepts_snapshot(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        snapshot_compare = self.base / "snap/pgo/audits/release_compare.py"
        snapshot_fixed_k = self.base / "snap/pgo/audits/fixed_k.py"
        result = self.run_release(
            cohort, pgo, nopgo,
            comparator=snapshot_compare, fixed_k=snapshot_fixed_k,
            require_snapshot_harness=True, git_root=ROOT)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        manifest = json.loads(
            (self.base / "release-out/manifest.json").read_text())
        self.assertEqual(
            Path(manifest["tooling"]["release_compare"]["path"]).resolve(),
            snapshot_compare.resolve())
        self.assertEqual(
            Path(manifest["tooling"]["fixed_k"]["path"]).resolve(),
            snapshot_fixed_k.resolve())

    def test_release_compare_snapshot_harness_pin_rejects_mismatch(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        tampered = self.base / "snap/nopgo/audits/fixed_k.py"
        tampered.write_text(tampered.read_text() + "# tampered\n",
                            encoding="utf-8")
        result = self.run_release(cohort, pgo, nopgo,
                                  require_snapshot_harness=True)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("harness mismatch", result.stdout + result.stderr)

    def test_release_compare_snapshot_harness_pin_rejects_override(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        fake = self.report_writer("fixed-k-harness-override", {})
        result = self.run_release(
            cohort, pgo, nopgo, fixed_k=fake,
            require_snapshot_harness=True)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("harness mismatch", result.stdout + result.stderr)

    def test_release_compare_incompatible_manifests_fails_closed(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(
            cohort, spec, toolchain_nopgo="leanprover/lean4:v9.99.0\n")
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("incompatible manifests",
                      result.stdout + result.stderr)
        comparison = json.loads(
            (self.base / "release-out/comparison.json").read_text())
        self.assertEqual(comparison["status"], "fail")

    def test_release_compare_extra_lakefile_change_fails_closed(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(
            cohort, spec, extra_nopgo="extra = true\n")
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("incompatible manifests",
                      result.stdout + result.stderr)

    def test_release_compare_missing_snapshot_fails_closed(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        result = self.run_release(
            cohort, pgo, nopgo,
            snapshot_pgo=self.base / "snap/absent")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("snapshot not found", result.stdout + result.stderr)

    def test_release_compare_missing_fixture_fails_closed(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        (self.base / "snap/nopgo/models/opt_case.fzn").unlink()
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("missing fixture", result.stdout + result.stderr)

    def test_release_compare_empty_cohort_fails_closed(self):
        self.sat_model()
        cohort = self.base / "empty.tsv"
        cohort.write_text(f"# conflict_limit: 10\n{HEADER}\n",
                          encoding="utf-8")
        pgo, nopgo = self.snapshots(cohort, self.sat_spec())
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("no data rows", result.stdout + result.stderr)

    def test_release_compare_unreadable_binary_fails_closed(self):
        spec, cohort = self.four_case_material()
        pgo, nopgo = self.snapshots(cohort, spec)
        pgo.chmod(0o644)
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("not executable", result.stdout + result.stderr)

    def test_release_compare_missing_stats_fails_closed(self):
        spec, cohort = self.four_case_material()
        spec["sat_case.fzn"].pop("stats")
        pgo, nopgo = self.snapshots(cohort, spec)
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("missing_stats", result.stdout + result.stderr)

    def test_release_compare_wrong_objective_fails_closed(self):
        spec, cohort = self.four_case_material()
        spec["opt_case.fzn"]["stdout"] = "z = 999 ;\n----------\n==========\n"
        pgo, nopgo = self.snapshots(cohort, spec)
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("wrong_objective", result.stdout + result.stderr)

    def test_release_compare_rejected_witness_fails_closed(self):
        spec, cohort = self.four_case_material()
        spec["check_rc"] = 1
        spec["check_stdout"] = "solution rejected: unsatisfied condition"
        pgo, nopgo = self.snapshots(cohort, spec)
        result = self.run_release(cohort, pgo, nopgo)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("rejected_witness", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
