"""Regress import-audit syntax and the public/legacy dependency boundary."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / 'audits/check_module_boundaries.py'


class ImportBoundaries(unittest.TestCase):
    def run_fixture(self, facade, extra_files=None):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            files = {
                'LeanFzn.lean': 'import LeanFzn.Cli.Main\n',
                'Main.lean': 'import LeanFzn.Cli.Main\n',
                'LeanFzn/Cli/Main.lean': '/- outer /- nested -/ -/import LeanFzn.Engine.Facade -- actual import\n',
                'LeanFzn/Engine/Facade.lean': facade,
                'LeanFzn/Engine/Safe.lean': '-- safe shared module\n',
                'LeanFzn/Legacy/Old.lean': '-- legacy is permitted to exist\n',
                'audits/check_module_boundaries.py': AUDIT.read_text(),
            }
            files.update(extra_files or {})
            for name, text in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            return subprocess.run(['python3', str(root / 'audits/check_module_boundaries.py')],
                                  text=True, capture_output=True, check=False)

    def test_comments_and_strings_are_not_imports(self):
        result = self.run_fixture('/- import LeanFzn.Legacy.Old -/\n'
                                  'def example := "import LeanFzn.Legacy.Old"\n')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_proof_hole_words_in_comments_and_strings_are_allowed(self):
        result = self.run_fixture('/- no sorry /- no admit -/ or axiom -/\n'
                                  'def example := "sorry admit axiom"\n')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_active_proof_holes_are_rejected(self):
        for hole in ('sorry', 'admit'):
            with self.subTest(hole=hole):
                result = self.run_fixture(f'theorem bad : False := by {hole}\n')
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('active proof hole or user axiom', result.stderr)

    def test_user_axioms_are_rejected(self):
        result = self.run_fixture('axiom bad : False\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('active proof hole or user axiom', result.stderr)

    def test_import_directly_after_comment_is_checked(self):
        result = self.run_fixture('/- comment -/import LeanFzn.Legacy.Old\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('LeanFzn.Cli.Main -> LeanFzn.Engine.Facade -> LeanFzn.Legacy.Old', result.stderr)

    def test_every_module_on_an_import_line_is_checked(self):
        result = self.run_fixture('import LeanFzn.Engine.Safe LeanFzn.Legacy.Old\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('LeanFzn.Legacy.Old', result.stderr)

    def test_missing_import_cannot_hide_a_dependency(self):
        result = self.run_fixture('import LeanFzn.Missing\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('imports missing module LeanFzn.Missing', result.stderr)

    def test_cycles_are_rejected(self):
        result = self.run_fixture('import LeanFzn.Cli.Main\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Import cycle:', result.stderr)

    def test_current_tests_cannot_import_legacy(self):
        result = self.run_fixture('', {
            'Tests/Engine/Search.lean': 'import LeanFzn.Legacy.Old\n',
        })
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Tests.Engine.Search -> LeanFzn.Legacy.Old', result.stderr)

    def test_current_tests_cannot_hide_legacy_behind_test_helpers(self):
        result = self.run_fixture('', {
            'Tests/Integration/Public/Runtime.lean': 'import Tests.Legacy.Helper\n',
            'Tests/Legacy/Helper.lean': 'import LeanFzn.Legacy.Old\n',
        })
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Tests.Integration.Public.Runtime -> Tests.Legacy.Helper', result.stderr)

    def test_explicit_legacy_tests_are_allowed(self):
        result = self.run_fixture('', {
            'Tests/Legacy/Solver/UIP/Search.lean': 'import LeanFzn.Legacy.Old\n',
        })
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_missing_test_helpers_are_rejected(self):
        result = self.run_fixture('', {
            'Tests/Engine/Search.lean': 'import Tests.Engine.Missing\n',
        })
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('imports missing module Tests.Engine.Missing', result.stderr)


if __name__ == '__main__':
    unittest.main()
