#!/usr/bin/env python3
"""D1 separator regressions: exact marker policy and `check` exit classes.

The solution stream splitter and separator stripper share the classifier in
`LeanFzn.Checker.Solution`.  These tests go through the compiled CLI so the
exit codes 0/1/4 and the "no solution in the input" distinction are exercised,
not just block counts.
"""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BIN = ROOT / '.lake/build/bin/leanfzn'

MODEL = 'var 0..9: x;\nconstraint int_le(x, 5);\nsolve satisfy;\n'
ZERO_VAR_MODEL = 'solve satisfy;\n'


class CheckSeparators(unittest.TestCase):
    def check(self, model, text):
        with tempfile.TemporaryDirectory() as tmp:
            model_path = Path(tmp) / 'case.fzn'
            solution_path = Path(tmp) / 'solution.txt'
            model_path.write_text(model)
            solution_path.write_text(text)
            return subprocess.run(
                [str(BIN), 'check', str(model_path), str(solution_path)],
                text=True, capture_output=True, timeout=60)

    def assertAccepted(self, result, stdout='solution accepted'):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(stdout, result.stdout)
        self.assertEqual(result.stderr, '')

    def test_unpadded_separator(self):
        self.assertAccepted(self.check(MODEL, 'x = 1;\n----------\n'))

    def test_padded_separator_and_crlf(self):
        self.assertAccepted(self.check(MODEL, '  x = 1;  \r\n\t----------\t\r\n'))

    def test_crlf_multiple_solutions(self):
        self.assertAccepted(
            self.check(MODEL, 'x = 1;\r\n----------\r\nx = 2;\r\n----------\r\n'),
            'all 2 solutions accepted')

    def test_status_only_is_exit_4(self):
        for text in ['=====UNSATISFIABLE=====\n',
                     '\t=====UNKNOWN===== \r\n',
                     '  =====ERROR=====\r\n']:
            with self.subTest(text=text):
                result = self.check(MODEL, text)
                self.assertEqual(result.returncode, 4,
                                 result.stdout + result.stderr)
                self.assertIn('no solution in the input', result.stderr)
                self.assertEqual(result.stdout, '')

    def test_blank_and_comment_only_exit_4(self):
        for text in ['', '\n\n \t\r\n', '% only a comment\n']:
            with self.subTest(text=text):
                result = self.check(MODEL, text)
                self.assertEqual(result.returncode, 4,
                                 result.stdout + result.stderr)
                self.assertIn('no solution in the input', result.stderr)
                self.assertEqual(result.stdout, '')

    def test_malformed_marker_prefixes_are_rejected(self):
        for text in ['x = 1;\n----------garbage\n',
                     'x = 1;\n==========garbage\n',
                     'x = 1;\n=====garbage\n']:
            with self.subTest(text=text):
                result = self.check(MODEL, text)
                self.assertEqual(result.returncode, 4,
                                 result.stdout + result.stderr)
                self.assertIn('malformed solution', result.stderr)
                self.assertEqual(result.stdout, '')

    def test_trailing_status_after_last_separator_is_ignored(self):
        self.assertAccepted(
            self.check(MODEL, 'x = 1;\n----------\n=====UNKNOWN=====\n'))

    def test_status_inside_a_candidate_is_rejected(self):
        result = self.check(MODEL, 'x = 1;\n=====UNKNOWN=====\n----------\n')
        self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
        self.assertIn('malformed solution', result.stderr)

    def test_bare_separator_zero_variable_model(self):
        self.assertAccepted(self.check(ZERO_VAR_MODEL, '----------\n'))

    def test_bare_separator_nonempty_model_is_unsatisfied(self):
        result = self.check(MODEL, '----------\n')
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('solution rejected', result.stdout)


if __name__ == '__main__':
    unittest.main()
