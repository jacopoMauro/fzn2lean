"""Regress distinct Core outcomes in the strategy matrix runner (R0.4).

`strategy_matrix.outcome_of` must keep timeouts, give-ups (exit 4, with and
without a retained incumbent) and completed runs apart.
"""
from pathlib import Path
import runpy
import unittest

TOOLS = runpy.run_path(
    str(Path(__file__).resolve().parents[2] / 'audits/strategy_matrix.py'))
outcome_of = TOOLS['outcome_of']


class StrategyOutcomes(unittest.TestCase):
    def test_exit_four_is_not_none(self):
        self.assertEqual(outcome_of(4, False, '', 0), 'unknown')
        self.assertEqual(outcome_of(4, False, '----------\n', 2),
                         'incomplete_with_incumbent')

    def test_timeout_is_separate_from_give_up(self):
        self.assertEqual(outcome_of(137, True, '', 0), 'timeout')
        self.assertEqual(outcome_of(137, True, '----------\n', 1),
                         'timeout_with_incumbent')

    def test_completed_runs(self):
        self.assertEqual(outcome_of(0, False, '', 0), 'none')
        self.assertEqual(outcome_of(0, False, '----------\n', 1), 'sat-incumbent')
        self.assertEqual(outcome_of(0, False, '==========\n', 1), 'proved')
        self.assertEqual(outcome_of(1, False, '=====UNSATISFIABLE=====\n', 0),
                         'proved')

    def test_terminal_markers_win_over_a_timeout(self):
        self.assertEqual(outcome_of(0, True, '==========\n', 1), 'proved')

    def test_unsupported_and_error(self):
        self.assertEqual(outcome_of(3, False, '', 0), 'unsupported')
        self.assertEqual(outcome_of(2, False, '', 0), 'error')


if __name__ == '__main__':
    unittest.main()
