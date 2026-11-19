#!/usr/bin/env python3
"""Actual-process `--report=jsonl-v1` tests (B2.4).

Every test runs the built CLI, decodes each stdout line as JSON and checks the
frozen protocol shape.  Solved streams are also re-emitted as FlatZinc solution
text and accepted by the independent `leanfzn check` front door, so a streamed
witness is verified, not merely well-formed.
"""
import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BIN = ROOT / '.lake/build/bin/leanfzn'

HANDSHAKE = {'event': 'handshake', 'protocol': 'leanfzn-report', 'version': 1}
TERMINAL_EXIT = {'sat': 0, 'optimal': 0, 'unsat': 1, 'incomplete': 4,
                 'unsupported': 3}
ERROR_EXIT = {'usage': 2, 'io': 2, 'model_parse': 2, 'unsupported': 3,
              'compile': 3, 'internal': 2}


class JsonlProtocol(unittest.TestCase):
    def solve(self, source, *flags):
        """Run one model; return (result, events, folder)."""
        folder = Path(tempfile.mkdtemp(prefix='jsonl-'))
        self.addCleanup(shutil.rmtree, folder, True)
        model = folder / 'case.fzn'
        model.write_text(source)
        result = subprocess.run(
            [str(BIN), 'solve', '--report=jsonl-v1', *flags, str(model)],
            text=True, capture_output=True, timeout=60)
        events = []
        if result.stdout:
            self.assertTrue(result.stdout.endswith('\n'), result.stdout)
            for line in result.stdout.splitlines():
                events.append(json.loads(line))
        return result, events, folder

    def stream(self, source, *flags):
        result, events, folder = self.solve(source, *flags)
        self.assertGreaterEqual(len(events), 1, result.stdout + result.stderr)
        self.assertEqual(events[0], HANDSHAKE)
        self.assertEqual(sum(e['event'] == 'handshake' for e in events), 1)
        outcomes = [e for e in events if e['event'] in ('terminal', 'error')]
        self.assertEqual(len(outcomes), 1, result.stdout)
        self.assertIs(events[-1], outcomes[0])
        terminal = events[-1]
        if terminal['event'] == 'error':
            self.assertEqual(terminal['exit'], ERROR_EXIT[terminal['kind']])
            self.assertEqual(result.returncode, terminal['exit'])
        else:
            self.assertEqual(terminal['exit'],
                             TERMINAL_EXIT[terminal['kind']])
            self.assertEqual(result.returncode, terminal['exit'])
        return result, events, folder, terminal

    def solutions(self, events):
        return [e for e in events if e['event'] == 'solution']

    def check_stream(self, folder, events, terminal):
        """Reconstruct the text stream and let `leanfzn check` accept it."""
        solutions = self.solutions(events)
        if not solutions:
            return
        text = ''.join('\n'.join(entry['text'] for entry in solution['entries'])
                       + '\n----------\n' for solution in solutions)
        if terminal['kind'] == 'optimal':
            text += '==========\n'
        path = folder / 'stream.sol'
        path.write_text(text)
        checked = subprocess.run(
            [str(BIN), 'check', str(folder / 'case.fzn'), str(path)],
            text=True, capture_output=True, timeout=60)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_sat_stream_and_checked_witness(self):
        result, events, folder, terminal = self.stream(
            'var 0..9: x :: output_var;\nvar 0..9: y :: output_var;\n'
            'constraint int_lt(x,y);\nsolve satisfy;\n')
        model = events[1]
        self.assertEqual(model['event'], 'model')
        self.assertEqual(model['mode'], 'satisfy')
        self.assertEqual(model['outputs'], ['x', 'y'])
        self.assertNotIn('objective', model)
        solutions = self.solutions(events)
        self.assertEqual(len(solutions), 1)
        self.assertEqual(solutions[0]['id'], 1)
        self.assertEqual([e['name'] for e in solutions[0]['entries']],
                         ['x', 'y'])
        self.assertNotIn('objective', solutions[0])
        self.assertEqual(terminal, {'event': 'terminal', 'kind': 'sat',
                                    'exit': 0})
        self.check_stream(folder, events, terminal)

    def test_unsat_makes_no_solution_claim(self):
        result, events, folder, terminal = self.stream(
            'var 0..1: x;\nconstraint int_eq(x,0);\n'
            'constraint int_eq(x,1);\nsolve satisfy;\n')
        self.assertEqual(self.solutions(events), [])
        self.assertEqual(terminal['kind'], 'unsat')
        self.assertEqual(result.returncode, 1)
        self.assertNotIn('UNSATISFIABLE', result.stdout)
        self.assertNotIn('----------', result.stdout)

    def test_optimization_multiple_improving_witnesses(self):
        result, events, folder, terminal = self.stream(
            'var 0..3: x :: output_var;\nsolve maximize x;\n')
        solutions = self.solutions(events)
        self.assertEqual([s['id'] for s in solutions], [1, 2, 3, 4])
        self.assertEqual([s['objective'] for s in solutions],
                         ['0', '1', '2', '3'])
        self.assertEqual([e['text'] for e in solutions[-1]['entries']],
                         ['x = 3 ; '])
        self.assertEqual(terminal['kind'], 'optimal')
        self.assertEqual(terminal['solution'], 4)
        self.check_stream(folder, events, terminal)

    def test_seeded_and_lns_routes(self):
        source = ('var 0..3: x :: output_var;\nvar bool: b;\n'
                  'constraint bool_clause([b],[]);\nsolve maximize x;\n')
        for flags in (('--opt=seeded',), ('--primal=lns',)):
            with self.subTest(flags=flags):
                _, events, folder, terminal = self.stream(source, *flags)
                self.assertEqual(terminal['kind'], 'optimal')
                self.assertEqual(terminal['solution'],
                                 len(self.solutions(events)))
                self.check_stream(folder, events, terminal)

    def test_portfolio_routes(self):
        sat = 'var 0..9: x :: output_var;\nsolve satisfy;\n'
        opt = 'var 0..3: x :: output_var;\nsolve minimize x;\n'
        for source, kind in ((sat, 'sat'), (opt, 'optimal')):
            with self.subTest(kind=kind):
                _, events, folder, terminal = self.stream(
                    source, '--threads=2')
                self.assertEqual(terminal['kind'], kind)
                self.check_stream(folder, events, terminal)

    def test_incomplete_stream_makes_no_proof_claim(self):
        result, events, folder, terminal = self.stream(
            'var 0..1: a;\nvar 0..1: b;\nvar 0..1: c;\n'
            'constraint int_ne(a,b);\nconstraint int_ne(a,c);\n'
            'constraint int_ne(b,c);\nsolve satisfy;\n',
            '--conflict-limit=1')
        self.assertEqual(terminal['kind'], 'incomplete')
        self.assertEqual(result.returncode, 4)
        self.assertNotIn('optimal', [e.get('kind') for e in events
                                     if e['event'] == 'terminal'])

    def test_unsupported_satisfaction_is_a_terminal_not_a_claim(self):
        result, events, folder, terminal = self.stream(
            'var 1..2: x :: output_var;\n'
            'constraint int_pow(x,2,x);\nsolve satisfy;\n')
        self.assertEqual(terminal['kind'], 'unsupported')
        self.assertIsInstance(terminal.get('reason'), str)
        self.assertEqual(result.returncode, 3)
        self.assertEqual(self.solutions(events), [])

    def test_compile_rejection_is_a_typed_error(self):
        result, events, folder, terminal = self.stream(
            'var 1..2: x :: output_var;\n'
            'constraint int_pow(x,2,x);\nsolve minimize x;\n')
        self.assertEqual(terminal['event'], 'error')
        self.assertEqual(terminal['kind'], 'compile')
        self.assertEqual(result.returncode, 3)
        self.assertNotIn('terminal', [e['event'] for e in events])

    def test_early_errors_are_typed_after_the_handshake(self):
        folder = Path(tempfile.mkdtemp(prefix='jsonl-'))
        self.addCleanup(shutil.rmtree, folder, True)
        model = folder / 'case.fzn'
        model.write_text('var 0..1: x :: output_var;\nsolve satisfy;\n')
        cases = [
            (['--nonsense', str(model)], 'usage'),
            ([str(folder / 'missing.fzn')], 'io'),
        ]
        bad = folder / 'bad.fzn'
        bad.write_text('var 1..3 x;\n')
        cases.append(([str(bad)], 'model_parse'))
        for args, kind in cases:
            with self.subTest(kind=kind):
                result = subprocess.run(
                    [str(BIN), 'solve', '--report=jsonl-v1', *args],
                    text=True, capture_output=True, timeout=60)
                events = [json.loads(line)
                          for line in result.stdout.splitlines()]
                self.assertEqual(events[0], HANDSHAKE)
                self.assertEqual(events[-1]['event'], 'error')
                self.assertEqual(events[-1]['kind'], kind)
                self.assertEqual(events[-1]['exit'], ERROR_EXIT[kind])
                self.assertEqual(result.returncode, ERROR_EXIT[kind])

    def test_large_integers_are_canonical_decimal_strings(self):
        _, events, folder, terminal = self.stream(
            'var 9999999999999999999..10000000000000000000: '
            'x :: output_var;\nsolve minimize x;\n')
        solution = self.solutions(events)[0]
        self.assertEqual(solution['objective'], '9999999999999999999')
        self.assertIn('9999999999999999999', solution['entries'][0]['text'])
        self.check_stream(folder, events, terminal)

    def test_empty_model_has_an_empty_solution_record(self):
        _, events, folder, terminal = self.stream('solve satisfy;\n')
        solutions = self.solutions(events)
        self.assertEqual(len(solutions), 1)
        self.assertEqual(solutions[0]['entries'], [])
        self.assertEqual(terminal['kind'], 'sat')
        self.check_stream(folder, events, terminal)

    def test_phase_stats_is_rejected_in_jsonl_mode(self):
        # `--phase-stats` runs unproved instrumentation twins; a JSONL proof
        # terminal must only come from the certified ordinary driver.
        result, events, folder, terminal = self.stream(
            'var 0..3: x :: output_var;\nsolve minimize x;\n',
            '--phase-stats')
        self.assertEqual(terminal['event'], 'error')
        self.assertEqual(terminal['kind'], 'usage')
        self.assertIn('--phase-stats', terminal['message'])

    def test_stats_and_phase_lines_stay_on_stderr(self):
        folder = Path(tempfile.mkdtemp(prefix='text-'))
        self.addCleanup(shutil.rmtree, folder, True)
        model = folder / 'case.fzn'
        model.write_text('var 0..3: x :: output_var;\nsolve minimize x;\n')
        result = subprocess.run(
            [str(BIN), 'solve', '--stats', '--phase-stats', str(model)],
            text=True, capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('leanfzn: stats:', result.stderr)
        self.assertIn('leanfzn: phase', result.stderr)
        self.assertIn('----------', result.stdout)
        self.assertIn('==========', result.stdout)

    def test_model_metadata_uses_parsed_annotations(self):
        source = (
            '% var 0..1: hidden :: output_var;\n'
            'var 0..1:\n x :: output_var;\n'
            'var 0..1: y :: output_var;\n'
            'var 0..1: z :: label("output_var; solve maximize z;");\n'
            'var 0..1: output_var;\n'
            'var 0..1: output_var_like :: output_var;\n'
            'solve satisfy;\n')
        _, events, folder, terminal = self.stream(source)
        model = events[1]
        self.assertEqual(model['outputs'],
                         ['x', 'y', 'output_var_like'])
        self.assertEqual(terminal['kind'], 'sat')

    def test_output_array_metadata_before_unsupported(self):
        _, events, folder, terminal = self.stream(
            'var 0..5: x :: output_var;\nvar 0..5: y :: output_var;\n'
            'array [1..2] of var 0..3: ys :: output_array([1..2]) = [x,y];\n'
            'constraint all_different(ys);\nsolve satisfy;\n')
        model = events[1]
        self.assertEqual(model['outputs'], ['x', 'y', 'ys'])
        self.assertEqual(terminal['kind'], 'unsupported')

    def test_invalid_report_value_is_plain_text(self):
        folder = Path(tempfile.mkdtemp(prefix='jsonl-'))
        self.addCleanup(shutil.rmtree, folder, True)
        model = folder / 'case.fzn'
        model.write_text('solve satisfy;\n')
        result = subprocess.run(
            [str(BIN), 'solve', '--report=yaml', str(model)],
            text=True, capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, '')
        self.assertIn('invalid value', result.stderr)


if __name__ == '__main__':
    unittest.main()
