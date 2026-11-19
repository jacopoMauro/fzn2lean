"""Public admitted-fragment regressions, including ground-folding bypasses.

Expected answers come from the pinned native contracts, not from comparing the
checker with itself. Rejected premises are unsupported (3), never UNSAT (1).
"""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BIN = ROOT / '.lake/build/bin/leanfzn'


class Admission(unittest.TestCase):
    def check_case(self, call, expected, declarations='', solution='admission_witness = 0;\n----------\n', solve=None):
        with tempfile.TemporaryDirectory() as folder:
            model = Path(folder) / 'model.fzn'
            witness = Path(folder) / 'solution.txt'
            model.write_text(declarations + '\nvar 0..0: admission_witness = 0;\nconstraint '
                             + call + ';\nsolve satisfy;\n')
            witness.write_text(solution)
            result = subprocess.run([str(BIN), 'check', str(model), str(witness)],
                                    text=True, capture_output=True, timeout=15)
            self.assertEqual(result.returncode, expected, (call, result.stdout, result.stderr))
            if solve is not None:
                result = subprocess.run([str(BIN), 'solve', str(model)],
                                        text=True, capture_output=True, timeout=15)
                self.assertEqual(result.returncode, solve, (call, result.stdout, result.stderr))
                if solve == 3:
                    self.assertNotIn('=====UNSATISFIABLE=====', result.stdout)
                    self.assertNotIn('==========', result.stdout)
                    for flags in [['--phase-stats'], ['--threads=2']]:
                        alternate = subprocess.run([str(BIN), 'solve', *flags, str(model)],
                                                   text=True, capture_output=True, timeout=15)
                        self.assertEqual(alternate.returncode, 3,
                                         (call, flags, alternate.stdout, alternate.stderr))
                        self.assertNotIn('=====UNSATISFIABLE=====', alternate.stdout)

    def test_packing_premises(self):
        for call, rc in [
            ('fzn_bin_packing(2,[1,1],[1,1])', 0),
            ('fzn_bin_packing(1,[1,1],[1,1])', 1),
            ('fzn_bin_packing(0,[],[])', 0),
            ('fzn_bin_packing(-1,[],[])', 3),
            ('fzn_bin_packing(1,[1],[-1])', 3),
            ('fzn_bin_packing(1,[1],[])', 3),
            ('fzn_bin_packing(1,[],[0])', 3),
            ('fzn_bin_packing(0,[1,1],[0,0])', 0),
        ]:
            with self.subTest(call=call): self.check_case(call, rc, solve=rc)

    def test_packing_declared_parameters_and_variable_bins(self):
        self.check_case('fzn_bin_packing(c,[x],w)', 0,
                        'int: c = 2; array [1..1] of int: w = [2]; var 1..2: x;',
                        'x = 1;\n----------\n')

    def test_cumulative_constant_premises(self):
        for call, rc in [
            ('fzn_cumulative([0],[1],[1],1)', 0),
            ('fzn_cumulative([],[],[],-1)', 0),
            ('fzn_cumulative([0],[0],[1],0)', 0),
            ('fzn_cumulative([0],[1],[0],0)', 0),
            ('fzn_cumulative([0],[1],[1],0)', 1),
            ('fzn_cumulative([0],[-1],[1],1)', 3),
            ('fzn_cumulative([0],[1],[-1],1)', 3),
            ('fzn_cumulative([0],[],[],1)', 3),
            ('fzn_cumulative([],[0],[],1)', 3),
        ]:
            with self.subTest(call=call): self.check_case(call, rc, solve=rc)

    def test_variable_cumulative_premise_is_explicitly_outside_fragment(self):
        self.check_case('fzn_cumulative([0],[d],[1],1)', 3,
                        'var 0..1: d;', 'd = 1;\n----------\n', solve=3)
        self.check_case('fzn_cumulative([0],duration,resource,1)', 0,
                        'array [1..1] of int: duration = [1]; '
                        'array [1..1] of int: resource = [1];', solve=0)

    def test_conditionally_masked_cumulatives_reads(self):
        for name in ['fzn_cumulatives', 'fzn_cumulatives_decomp']:
            for args, rc in [
                ('[],[],[],[],[],true', 0),
                ('[0],[1],[1],[1],[1],true', 0),
                ('[0],[1],[1],[1],[0],true', 1),
                ('[0],[],[],[],[],true', 3),
                ('[0],[1],[],[1],[],true', 3),
                ('[0],[1],[1],[],[],true', 3),
                ('[0],[0],[1],[0],[],true', 3),
                ('[0],[1],[1],[2],[1],true', 3),
                ('[0],[-1],[1],[1],[1],true', 0),
            ]:
                call = f'{name}({args}' + (',1)' if name == 'fzn_cumulatives' else ')')
                with self.subTest(call=call): self.check_case(call, rc, solve=rc)
        self.check_case('fzn_cumulatives([],[],[],[],[],true,5)', 3, solve=3)

    def test_regular_flat_matrix_abi(self):
        for name, matrix, suffix in [
            ('fzn_regular', '[1]', ''),
            ('fzn_regular_nfa', '[{1}]', ''),
            ('fzn_cost_regular', '[1]', ',[2],2'),
        ]:
            base = f'{name}([1],1,1,{matrix},1,{{1}}{suffix})'
            with self.subTest(call=base): self.check_case(base, 0, solve=0)
            bad = f'{name}([1],1,1,[],1,{{1}}{suffix})'
            with self.subTest(call=bad): self.check_case(bad, 3, solve=3)
        for call, rc in [
            ('fzn_regular([],0,0,[],7,{7})', 0),
            ('fzn_regular([],0,0,[],7,{})', 1),
            ('fzn_regular([],-1,0,[],1,{1})', 3),
            ('fzn_regular([0],1,1,[1],1,{1})', 1),
            ('fzn_regular([2],1,1,[1],1,{1})', 1),
            ('fzn_regular([1],1,1,[2],1,{1})', 1),
            ('fzn_regular([1],1,1,[1],0,{1})', 1),
            ('fzn_cost_regular([1],1,1,[1],1,{1},[],2)', 3),
            ('fzn_regular_nfa([1],1,1,[{}],1,{1})', 1),
        ]:
            with self.subTest(call=call): self.check_case(call, rc, solve=rc)

    def test_unresolved_native_contracts_are_unsupported_even_when_ground(self):
        for call in [
            'fzn_geost(1,[1],[0],[{1}],[0],[1])',
            'fzn_geost(0,[],[],[],[],[])',
            'fzn_geost_bb(1,[1],[0],[{1}],[0],[1],[0],[1])',
            'fzn_geost_smallest_bb(1,[1],[0],[{1}],[0],[1],[0],[1])',
            'fzn_mdd_nondet([1],1,[1],1,[1],[{1}],[0])',
            'fzn_mdd_nondet([],0,[],0,[],[],[])',
            'fzn_cost_mdd([1],1,[1],1,[1],[{1}],[0],[0],0)',
            'fzn_cost_mdd([],0,[],0,[],[],[],[],0)',
        ]:
            with self.subTest(call=call): self.check_case(call, 3, solve=3)

    def test_closed_cardinality_aggregate_is_not_redundant(self):
        for call, rc in [
            ('fzn_global_cardinality_low_up_closed([1],[1],[1],[1])', 0),
            ('fzn_global_cardinality_low_up_closed([],[],[],[])', 0),
            ('fzn_global_cardinality_low_up_closed([],[1],[0],[0])', 0),
            ('fzn_global_cardinality_low_up_closed([],[1],[1],[1])', 3),
            ('fzn_global_cardinality_low_up_closed([],[1],[-1],[-1])', 3),
            ('fzn_global_cardinality_low_up_closed([1],[1,1],[1,1],[1,1])', 1),
            ('fzn_global_cardinality_low_up_closed([1],[1],[1,1],[1,1])', 3),
            ('fzn_global_cardinality_low_up_closed([1],[1],[0],[1,-1])', 3),
            ('fzn_global_cardinality_low_up_closed([1],[1,2],[0],[1,1])', 3),
        ]:
            with self.subTest(call=call): self.check_case(call, rc, solve=rc)

    def test_optimization_enforces_same_source_admission(self):
        with tempfile.TemporaryDirectory() as folder:
            model = Path(folder) / 'optimization.fzn'
            model.write_text('var 0..1: objective;\n'
                             'constraint fzn_geost(1,[1],[0],[{1}],[0],[1]);\n'
                             'solve minimize objective;\n')
            for flags in [[], ['--opt=seeded'], ['--phase-stats'], ['--threads=2']]:
                with self.subTest(flags=flags):
                    result = subprocess.run([str(BIN), 'solve', *flags, str(model)],
                                            text=True, capture_output=True, timeout=15)
                    self.assertEqual(result.returncode, 3, (result.stdout, result.stderr))
                    self.assertNotIn('==========', result.stdout)

    def test_non_one_based_indices_are_rejected_by_parser(self):
        self.check_case('fzn_bin_packing(1,x,[1])', 2,
                        'array [0..0] of var 1..1: x = [1];', solve=2)


if __name__ == '__main__':
    unittest.main()
