"""Regress explicit Core unknowns without disguising lost completion or false claims."""
from pathlib import Path
import runpy
import unittest

TOOLS = runpy.run_path(str(Path(__file__).resolve().parents[2] / 'audits/benchmark_performance.py'))
classify = TOOLS['classify_outcome']
permitted = TOOLS['permitted_incomplete']


class PerformanceOutcomes(unittest.TestCase):
    def test_core_give_up_is_unknown(self):
        self.assertEqual(classify(4, False, 0, False, False), 'unknown')

    def test_incomplete_retains_incumbents(self):
        self.assertEqual(classify(4, False, 2, False, False), 'incomplete_with_incumbent')

    def test_incomplete_cannot_claim_terminal_results(self):
        self.assertEqual(classify(4, False, 0, True, False), 'error')
        self.assertEqual(classify(4, False, 1, False, True), 'error')

    def test_terminal_claims_keep_their_required_markers(self):
        self.assertEqual(classify(1, False, 0, True, False), 'unsat')
        self.assertEqual(classify(0, False, 1, False, True), 'sat')
        self.assertEqual(classify(1, False, 0, False, False), 'error')

    def test_unknown_allowance_is_explicit_and_does_not_allow_false_sat(self):
        case = {'expected': 'unsat', 'allow_incomplete': True}
        self.assertTrue(permitted(case, {'outcome': 'unknown', 'solutions': 0}))
        self.assertFalse(permitted({'expected': 'unsat'}, {'outcome': 'unknown', 'solutions': 0}))
        self.assertFalse(permitted(case, {'outcome': 'incomplete_with_incumbent', 'solutions': 1}))
        self.assertEqual(case['expected'], 'unsat')


if __name__ == '__main__':
    unittest.main()
