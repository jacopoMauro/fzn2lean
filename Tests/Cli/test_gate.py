"""P0 gate regression: refused inputs must keep today's exit codes and never
print a verdict marker.

The gate is now the single admission/well-formedness/printable-name decision:
an ill-formed model (wrong argument type) must exit 2 (model parse), and a
non-admitted native contract must exit 3 (unsupported scope).  Neither may
print `=====UNSATISFIABLE=====` or `==========`, on any driver path (plain,
`--phase-stats`, `--threads=2`).
"""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BIN = ROOT / '.lake/build/bin/leanfzn'


def solve(text, *flags):
    with tempfile.TemporaryDirectory() as folder:
        model = Path(folder) / 'model.fzn'
        model.write_text(text)
        return subprocess.run([str(BIN), 'solve', *flags, str(model)],
                              text=True, capture_output=True, timeout=30)


class GateExitCodes(unittest.TestCase):
    def assertVerdictFree(self, text, expected, *flags):
        result = solve(text, *flags)
        self.assertEqual(result.returncode, expected,
                         (text, flags, result.stdout, result.stderr))
        self.assertNotIn('=====UNSATISFIABLE=====', result.stdout)
        self.assertNotIn('==========', result.stdout)

    def test_ill_formed_argument_is_a_parse_failure(self):
        text = ('var 0..4: x :: output_var;\n'
                'var bool: b = true;\n'
                'constraint int_eq(x, b);\n'
                'solve satisfy;\n')
        for flags in [(), ('--phase-stats',), ('--threads=2',)]:
            with self.subTest(flags=flags):
                self.assertVerdictFree(text, 2, *flags)

    def test_unprintable_name_is_unsupported_scope(self):
        text = ('var 0..4: x :: output_var;\n'
                'var 0..4: \'not a name\' :: output_var;\n'
                'solve satisfy;\n')
        with self.subTest(flags=()):
            result = solve(text)
            self.assertIn(result.returncode, (2, 3),
                          (result.stdout, result.stderr))
            self.assertNotIn('=====UNSATISFIABLE=====', result.stdout)

    def test_non_admitted_contract_is_unsupported_scope(self):
        text = ('var 0..4: r :: output_var;\n'
                'constraint fzn_cost_mdd([1],1,[1],1,[1],[{1}],[0],[0],r);\n'
                'solve satisfy;\n')
        for flags in [(), ('--phase-stats',)]:
            with self.subTest(flags=flags):
                self.assertVerdictFree(text, 3, *flags)

    def test_admitted_model_still_solves(self):
        result = solve('var 0..4: x :: output_var;\nconstraint int_eq(x, 2);\n'
                       'solve satisfy;\n')
        self.assertEqual(result.returncode, 0, (result.stdout, result.stderr))
        self.assertIn('x = 2', result.stdout)


if __name__ == '__main__':
    unittest.main()
