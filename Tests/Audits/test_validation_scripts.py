"""Validation must reject stale binaries and missing/failed solver runs."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class ValidationScripts(unittest.TestCase):
    def executable(self, path, source):
        path.write_text('#!/usr/bin/env python3\n' + source)
        path.chmod(0o755)
        return path

    def smoke(self, mode):
        with tempfile.TemporaryDirectory() as tmp:
            folder = Path(tmp)
            mzn = self.executable(folder / 'minizinc', '''import os, sys
if '--version' in sys.argv:
    print('MiniZinc version 2.10.0')
elif '-c' in sys.argv:
    sys.exit(1 if os.environ['TEST_MODE'] == 'compile_failure' else 0)
else:
    print('q = [1]\\nvalue = 51\\n==========\\n=====UNSATISFIABLE=====\\n=====UNSUPPORTED=====\\nlength = 6\\n%%%mzn-stat: failures=0')
    sys.exit(1 if os.environ['TEST_MODE'] == 'run_failure' else 0)
''')
            solver = self.executable(folder / 'leanfzn', '''import os, sys
if sys.argv[1] == 'solve':
    if os.environ['TEST_MODE'] != 'empty_solution':
        print('x = 1;\\n----------')
    sys.exit(1 if os.environ['TEST_MODE'] == 'solve_failure' else 0)
# A checker may accept zero supplied solutions. The smoke script must
# independently require a successful solve and a complete solution block.
''')
            return subprocess.run(
                ['bash', str(ROOT / 'minizinc-wrapper/test.sh'), str(mzn)],
                env={**os.environ, 'LEANFZN_BIN': str(solver), 'TEST_MODE': mode},
                text=True, capture_output=True, timeout=20)

    def test_smoke_accepts_successful_checked_solutions(self):
        result = self.smoke('ok')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_smoke_rejects_failures_and_empty_solutions(self):
        for mode in ['compile_failure', 'run_failure', 'solve_failure', 'empty_solution']:
            with self.subTest(mode=mode):
                result = self.smoke(mode)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_gate_stops_after_failed_build(self):
        with tempfile.TemporaryDirectory() as tmp:
            folder = Path(tmp)
            self.executable(folder / 'lake', 'raise SystemExit(1)\n')
            log = folder / 'logs'
            result = subprocess.run(
                ['bash', str(ROOT / 'audits/run_gates.sh'), str(log)],
                env={**os.environ, 'PATH': str(folder) + os.pathsep + os.environ['PATH']},
                text=True, capture_output=True, timeout=20)
            self.assertNotEqual(result.returncode, 0)
            # The oracle gate runs first and records its log; the build gate
            # then fails and stops the run.
            self.assertEqual(sorted(p.name for p in log.iterdir()),
                             ['build.log', 'oracles.log'])
            self.assertIn('build (see', result.stdout)
            self.assertNotIn('build: PASS', result.stdout)

    def test_gate_stops_after_failed_semantic_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            folder = Path(tmp)
            audit = folder / 'audits/run_gates.sh'
            audit.parent.mkdir()
            audit.write_text((ROOT / 'audits/run_gates.sh').read_text())
            (audit.parent / 'check_semantic_inventory.py').write_text(
                'import sys\nassert "--require-clean" in sys.argv\n'
                'raise SystemExit(1)\n')
            self.executable(folder / 'lake', 'raise SystemExit(0)\n')
            log = folder / 'logs'
            result = subprocess.run(
                ['bash', str(audit), str(log)],
                env={**os.environ, 'PATH': str(folder) + os.pathsep + os.environ['PATH']},
                text=True, capture_output=True, timeout=20)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('semantic-inventory', result.stdout)
            self.assertEqual(sorted(p.name for p in log.iterdir()),
                             ['build.log', 'oracles.log', 'repo-minimal.log',
                              'semantics.log'])

    def test_challenge_compilation_handles_spaces_and_reports_failure(self):
        for fails in (False, True):
            with self.subTest(fails=fails), tempfile.TemporaryDirectory() as tmp:
                folder = Path(tmp)
                script = folder / 'compile_fzn.sh'
                script.write_text((ROOT / 'minizinc-challenge/compile_fzn.sh').read_text())
                inputs = folder / '2025mzn/problem with spaces'
                inputs.mkdir(parents=True)
                (inputs / 'model.mzn').write_text('solve satisfy;')
                (inputs / 'instance with spaces.dzn').write_text('')
                compiler = self.executable(folder / 'minizinc', '''import sys
from pathlib import Path
assert len([a for a in sys.argv if a.endswith('.dzn')]) == 1
Path(sys.argv[sys.argv.index('-o') + 1]).write_text('solve satisfy;')
raise SystemExit(''' + ('1' if fails else '0') + ')\n')
                result = subprocess.run(
                    ['bash', str(script), '2025'],
                    env={**os.environ, 'MINIZINC_BIN': str(compiler)},
                    text=True, capture_output=True, timeout=20)
                output = folder / '2025fzn/problem with spaces/instance with spaces.fzn'
                self.assertEqual(result.returncode, 1 if fails else 0, result.stdout)
                self.assertEqual(output.exists(), not fails)


if __name__ == '__main__':
    unittest.main()
