#!/usr/bin/env python3
"""Compatibility checks for the wrapper's preserved flag and timeout behaviour.

B3 replaced the FlatZinc text scanner (`scan_model`, `ASSIGN_RE`, the old
`PARSE_ERROR_PREFIX` inference and unconditional marker pass-through) with the
frozen jsonl-v1 state machine in `specification/solver_protocol.md`.  The old
text-output expectations therefore no longer describe the wrapper interface;
the full protocol matrix lives in `Tests/Audits/test_wrapper_protocol.py`.
This module keeps the historical module name and re-tests the three preserved
intents (parallel flag forwarding, a timeout after a committed terminal, and a
timeout without a verdict) through a minimal JSONL mock.

"""

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WRAPPER = ROOT / 'minizinc-wrapper/fzn-leanfzn'

HANDSHAKE = ('{"event":"handshake","protocol":"leanfzn-report","version":1}')
MODEL = '{"event":"model","mode":"satisfy","outputs":["x"]}'
SOLUTION = ('{"event":"solution","id":1,'
            '"entries":[{"name":"x","text":"x = 1 ; "}]}')
TERMINAL = '{"event":"terminal","kind":"sat","exit":0}'


class MiniZincWrapper(unittest.TestCase):
    def run_solver(self, body, *flags):
        with tempfile.TemporaryDirectory() as tmp:
            folder = Path(tmp)
            solver = folder / 'solver'
            solver.write_text('#!/usr/bin/env python3\n' + body)
            solver.chmod(0o755)
            model = folder / 'model.fzn'
            model.write_text('var 0..1: x :: output_var; solve satisfy;\n')
            return subprocess.run(
                [str(WRAPPER), *flags, str(model)],
                env={**os.environ, 'LEANFZN_BIN': str(solver),
                     'FZN_LEANFZN_SAVE_DIR': ''},
                text=True, capture_output=True, timeout=10)

    def test_satisfaction_parallel_flag_reaches_core(self):
        folder = tempfile.TemporaryDirectory(prefix='wrapper-argv-')
        self.addCleanup(folder.cleanup)
        argv = Path(folder.name) / 'argv.json'
        result = self.run_solver(
            "import json, sys\n"
            f"json.dump(sys.argv, open({str(argv)!r}, 'w'))\n"
            f"print({HANDSHAKE!r}, flush=True)\n"
            f"print({MODEL!r}, flush=True)\n"
            f"print({SOLUTION!r}, flush=True)\n"
            f"print({TERMINAL!r}, flush=True)\n",
            '-p', '4')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, 'x = 1 ; \n----------\n')
        passed = json.loads(argv.read_text())
        self.assertIn('--report=jsonl-v1', passed)
        self.assertIn('--threads=4', passed)

    def test_timeout_after_terminal_marker_does_not_add_unknown(self):
        result = self.run_solver(
            "import time\n"
            f"print({HANDSHAKE!r}, flush=True)\n"
            f"print({MODEL!r}, flush=True)\n"
            "print('{\"event\":\"terminal\",\"kind\":\"unsat\",\"exit\":1}',"
            " flush=True)\n"
            "time.sleep(5)\n",
            '-t', '500')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, '=====UNSATISFIABLE=====\n')
        self.assertNotIn('=====UNKNOWN=====', result.stdout)

    def test_timeout_after_committed_completion_retains_it(self):
        result = self.run_solver(
            "import time\n"
            f"print({HANDSHAKE!r}, flush=True)\n"
            f"print({MODEL!r}, flush=True)\n"
            f"print({SOLUTION!r}, flush=True)\n"
            f"print({TERMINAL!r}, flush=True)\n"
            "time.sleep(5)\n",
            '-t', '500')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, 'x = 1 ; \n----------\n')

    def test_timeout_without_verdict_reports_unknown(self):
        result = self.run_solver('import time\ntime.sleep(5)\n', '-t', '100')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, '=====UNKNOWN=====\n')


if __name__ == '__main__':
    unittest.main()
