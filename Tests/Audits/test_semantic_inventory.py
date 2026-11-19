"""Fail-closed regression checks for semantic review coverage and provenance."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from audits import check_semantic_inventory as audit


class SemanticInventory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = json.loads(audit.INVENTORY.read_text())

    def setUp(self):
        self.data = copy.deepcopy(self.original)

    def errors(self, **kwargs):
        return '\n'.join(audit.check(self.data, **kwargs))

    def test_current_inventory_is_fresh(self):
        self.assertEqual(self.errors(), '')

    def test_restricted_row_requires_admission_policy(self):
        row = next(r for r in self.data['predicates'] if r['status'] == 'restricted')
        del row['admission']
        self.assertIn('missing explicit admission policy', self.errors())

    def test_admission_policy_requires_regression_evidence(self):
        row = next(r for r in self.data['predicates'] if r['status'] == 'restricted')
        row['admission']['regressions'] = ['Tests/Cli/does_not_exist.py']
        self.assertIn('admission regression missing', self.errors())

    def test_admission_policy_requires_checker_and_solver_scopes(self):
        row = next(r for r in self.data['predicates'] if r['status'] == 'restricted')
        del row['admission']['solver_scope']
        self.assertIn('admission missing solver_scope', self.errors())

    def test_restricted_model_rule_requires_admission_evidence(self):
        row = next(r for r in self.data['model_rules'] if r['status'] == 'restricted')
        del row['admission']
        self.assertIn('missing model admission evidence', self.errors())

    def test_missing_implemented_predicate_fails(self):
        self.data['predicates'] = [r for r in self.data['predicates'] if r['name'] != 'int_eq']
        self.assertIn('signature coverage differs', self.errors())

    def test_missing_unsupported_builtin_still_fails(self):
        self.data['predicates'] = [r for r in self.data['predicates'] if r['name'] != 'float_abs']
        self.assertIn('published builtin/function rows missing', self.errors())

    def test_missing_excluded_global_still_fails(self):
        self.data['predicates'] = [r for r in self.data['predicates'] if r['name'] != 'fzn_span']
        self.assertIn('explicitly excluded global rows missing', self.errors())

    def test_new_active_name_requires_review(self):
        active = audit.active_signatures()
        with patch.object(audit, 'active_signatures', return_value={**active, 'new_predicate': ['[]']}):
            self.assertIn('new_predicate', self.errors())

    def test_changed_signature_fails(self):
        row = next(r for r in self.data['predicates'] if r['name'] == 'int_eq')
        row['lean_signature'] = ['[]']
        self.assertIn('signature changed', self.errors())

    def test_helper_change_invalidates_review(self):
        # A helper change must invalidate the review even if predicate names
        # and signatures remain identical.
        self.data['reviewed_files']['LeanFzn/Semantics/Model.lean'] = '0' * 64
        self.assertIn('review is stale', self.errors())

    def test_removing_helper_hash_cannot_hide_a_change(self):
        del self.data['reviewed_files']['LeanFzn/Semantics/Globals/Common.lean']
        self.assertIn('missing reviewed source hashes', self.errors())

    def test_wrong_upstream_tree_fails(self):
        with tempfile.TemporaryDirectory() as folder:
            self.assertIn('upstream evidence mismatch', self.errors(upstream_root=Path(folder)))

    def test_review_cannot_hide_an_open_finding(self):
        # All real findings are fixed at close-out; inject the open state to
        # keep the fail-closed rule covered.
        row = next(r for r in self.data['predicates'] if r['findings'])
        finding = next(f for f in self.data['findings']
                       if f['id'] == row['findings'][0])
        finding['state'] = 'open'
        row['status'] = 'reviewed'
        self.assertIn('unresolved finding cannot be marked reviewed', self.errors())

    def test_unlinked_finding_fails(self):
        row = next(r for r in self.data['predicates'] if r['name'] == 'fzn_regular')
        row['findings'] = []
        self.assertIn('missing reverse link', self.errors())

    def test_clean_gate_rejects_known_semantic_gaps(self):
        # All real findings are fixed at close-out; inject one to keep the
        # fail-closed gate regression alive.
        self.data['findings'][0]['state'] = 'open'
        self.assertIn(f"open finding: {self.data['findings'][0]['id']}",
                      self.errors(require_clean=True))


if __name__ == '__main__':
    unittest.main()
