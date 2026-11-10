#!/usr/bin/env python3
"""Public CLI regressions: Core-only routing, incomplete output and checked witnesses."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BIN = ROOT / '.lake/build/bin/leanfzn'


class CoreOnlyCLI(unittest.TestCase):
    def solve(self, source, *flags):
        with tempfile.TemporaryDirectory() as tmp:
            model = Path(tmp) / 'case.fzn'
            model.write_text(source)
            result = subprocess.run([str(BIN), 'solve', *flags, str(model)],
                                    text=True, capture_output=True, timeout=20)
            if result.stdout.count('----------'):
                solution = Path(tmp) / 'solution.txt'
                solution.write_text(result.stdout)
                checked = subprocess.run([str(BIN), 'check', str(model), str(solution)],
                                         text=True, capture_output=True, timeout=20)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            return result

    def test_sparse_satisfaction_is_solved(self):
        source = 'var {0,1000000}: x :: output_var; solve satisfy;'
        for flags in [(), ('--engine=core',)]:
            with self.subTest(flags=flags):
                result = self.solve(source, *flags, '--stats')
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertTrue(result.stdout.rstrip().endswith('----------'), result.stdout)
                self.assertIn('x = 0;', result.stdout)
                self.assertIn('complete=1', result.stderr)
                self.assertIn('gaveUp=0', result.stderr)

    def test_sparse_optimization_is_complete(self):
        for strategy in ['linear', 'seeded']:
            with self.subTest(strategy=strategy):
                result = self.solve('var {0,1000000}: x :: output_var; solve minimize x;',
                                    '--opt=' + strategy, '--stats')
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertTrue(result.stdout.rstrip().endswith('=========='), result.stdout)
                self.assertIn('x = 0;', result.stdout)
                self.assertIn('complete=1', result.stderr)
                self.assertIn('gaveUp=0', result.stderr)

    def test_core_variable_strategies_are_accepted(self):
        for strategy in ['minc', 'annot', 'act', 'domwdeg', 'wdeg']:
            with self.subTest(strategy=strategy):
                result = self.solve('var {0,1000000}: x :: output_var; solve satisfy;',
                                    '--var=' + strategy, '--stats')
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertTrue(result.stdout.rstrip().endswith('----------'), result.stdout)
                self.assertIn('x = 0;', result.stdout)
                self.assertIn('complete=1', result.stderr)

    def test_completed_optimization_retains_certified_markers(self):
        for strategy in ['linear', 'seeded']:
            for direction, optimum in [('minimize', 0), ('maximize', 2)]:
                with self.subTest(strategy=strategy, direction=direction):
                    result = self.solve(f'var 0..2: x :: output_var; solve {direction} x;',
                                        '--opt=' + strategy, '--stats')
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertTrue(result.stdout.rstrip().endswith('=========='), result.stdout)
                    self.assertIn(f'x = {optimum};', result.stdout)
                    self.assertIn('complete=1', result.stderr)

    def test_sat_and_unsat(self):
        result = self.solve('var 0..2: x :: output_var; solve satisfy;')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.rstrip().endswith('----------'))
        result = self.solve('var 0..1: x; constraint int_eq(x,0); constraint int_eq(x,1); solve satisfy;')
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertEqual(result.stdout.strip(), '=====UNSATISFIABLE=====')

    def test_false_ground_constraint_is_unsat(self):
        result = self.solve('var 0..2: x; constraint int_eq(1,2); solve satisfy;')
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertEqual(result.stdout.strip(), '=====UNSATISFIABLE=====')

    def test_true_ground_constraint_is_dropped(self):
        result = self.solve('constraint int_eq(2,2); solve satisfy;')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), '----------')

    def test_literal_reification_result_reaches_search(self):
        result = self.solve(
            'var 0..2: x :: output_var; var 0..2: y :: output_var; '
            'constraint int_eq_reif(x,y,true); constraint int_eq(x,0); solve satisfy;')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('x = 0;', result.stdout)
        self.assertIn('y = 0;', result.stdout)

    def test_linear_false_literal_result_stays_unsupported(self):
        result = self.solve(
            'var 0..2: x; var 0..2: y; '
            'constraint int_lin_eq_reif([1,-1],[x,y],0,false); solve satisfy;')
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertIn('unsupported', result.stderr)

    def test_conflict_limit_gives_up_with_counters(self):
        result = self.solve(
            'var 0..1: a; var 0..1: b; var 0..1: c; '
            'constraint int_ne(a,b); constraint int_ne(a,c); constraint int_ne(b,c); '
            'solve satisfy;', '--conflict-limit=1', '--stats')
        self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
        self.assertNotIn('=====', result.stdout)
        self.assertNotIn('----------', result.stdout)
        self.assertIn('conflicts=1', result.stderr)
        self.assertIn('gaveUp=1', result.stderr)
        self.assertIn('cause="conflict limit reached"', result.stderr)

    def test_portfolio_solves_small_optimization(self):
        for threads in [2, 4, 8]:
            for direction, optimum in [('minimize', 0), ('maximize', 2)]:
                with self.subTest(threads=threads, direction=direction):
                    result = self.solve(
                        f'var 0..2: x :: output_var; solve {direction} x;',
                        f'--threads={threads}', '--stats')
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertTrue(result.stdout.rstrip().endswith('=========='), result.stdout)
                    self.assertIn(f'x = {optimum};', result.stdout)
                    self.assertIn('complete=1', result.stderr)
                    self.assertNotIn('does not match', result.stderr)

    def test_one_thread_keeps_the_ordinary_output(self):
        source = 'var 0..2: x :: output_var; solve minimize x;'
        ordinary = self.solve(source)
        explicit = self.solve(source, '--threads=1')
        self.assertEqual(explicit.returncode, ordinary.returncode)
        self.assertEqual(explicit.stdout, ordinary.stdout)
        self.assertEqual(explicit.stderr, ordinary.stderr)

    def test_portfolio_rejects_conflicting_or_out_of_range_flags(self):
        for flags, message in [
                (['--threads=0'], 'must be positive'),
                (['--threads=9'], 'limited to 8 workers'),
                (['--threads=4', '--strategy=annot'], 'cannot be combined with'),
                (['--threads=4', '--var=wdeg'], 'do not combine it with'),
                (['--threads=4', '--val=incumbent'], 'do not combine it with'),
                (['--threads=4', '--opt=seeded'], "requires '--opt=linear'"),
                (['--threads=4', '--primal=lns'], 'cannot be combined with'),
        ]:
            with self.subTest(flags=flags):
                result = subprocess.run(
                    [str(BIN), 'solve', *flags, '/nonexistent/core-only-test.fzn'],
                    text=True, capture_output=True, timeout=10)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertEqual(result.stdout, '')
                self.assertIn(message, result.stderr)
                self.assertNotIn('cannot read', result.stderr)

    def test_portfolio_solves_satisfaction_models(self):
        result = self.solve('var 0..2: x :: output_var; solve satisfy;', '--threads=2')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue(result.stdout.rstrip().endswith('----------'), result.stdout)
        result = self.solve(
            'var 0..1: x; constraint int_eq(x,0); constraint int_eq(x,1); solve satisfy;',
            '--threads=2')
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(result.stdout.strip(), '=====UNSATISFIABLE=====')

    def test_incomplete_portfolio_does_not_claim(self):
        source = (
            'var bool: x1; var bool: x2; var bool: x3; var bool: x4; var bool: x5; '
            'var bool: x6; var 0..1: obj :: output_var; '
            'constraint bool_clause([x1,x2],[]); constraint bool_clause([x3,x4],[]); '
            'constraint bool_clause([x5,x6],[]); '
            'constraint bool_clause([],[x1,x3]); constraint bool_clause([],[x1,x5]); '
            'constraint bool_clause([],[x3,x5]); constraint bool_clause([],[x2,x4]); '
            'constraint bool_clause([],[x2,x6]); constraint bool_clause([],[x4,x6]); '
            'solve minimize obj;')
        result = self.solve(source, '--threads=2', '--conflict-limit=1', '--stats')
        self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
        self.assertNotIn('=====', result.stdout)
        self.assertNotIn('==========', result.stdout)
        self.assertIn('incomplete', result.stderr)

    def test_conflict_limit_must_be_positive(self):
        result = subprocess.run(
            [str(BIN), 'solve', '--conflict-limit=0', '/nonexistent/core-only-test.fzn'],
            text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertEqual(result.stdout, '')
        self.assertIn('must be positive', result.stderr)

    def test_removed_certified_option_is_unknown(self):
        result = subprocess.run([str(BIN), 'solve', '--certified', '/nonexistent/core-only-test.fzn'],
                                text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertEqual(result.stdout, '')
        self.assertIn("unknown option '--certified'", result.stderr)

    def test_legacy_options_are_errors_before_model_loading(self):
        for flag in ['--engine=kernel', '--time-limit=10', '--var=obj', '--opt=bisect',
                     '--primal=dive', '--heur-act', '--portfolio=opt-fast:1,opt-fast']:
            with self.subTest(flag=flag):
                result = subprocess.run([str(BIN), 'solve', flag, '/nonexistent/core-only-test.fzn'],
                                        text=True, capture_output=True, timeout=10)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertEqual(result.stdout, '')
                self.assertNotIn('cannot read', result.stderr)


if __name__ == '__main__':
    unittest.main()
