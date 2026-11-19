#!/usr/bin/env python3
"""The minimal-repo audit must fail on coordination artifacts and orphans.

Each case builds a throw-away git repository with the audit script and a few
tracked files, then asserts that only the intended rule fires.  A check that
cannot fail is not a check, so the orphan case and the tracked-artifact case
are both exercised, together with a clean repository that must pass.
"""
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / 'audits/check_repo_minimal.py'


class RepoMinimal(unittest.TestCase):
    def repo(self, files):
        folder = Path(tempfile.mkdtemp())
        (folder / 'audits').mkdir()
        (folder / 'audits/check_repo_minimal.py').write_text(SCRIPT.read_text())
        # A closed reference graph over four files: run.sh cites the audit and
        # the helper, the helper cites run.sh again, and the README cites the
        # helper.  None of the allow-listed files is named, so the allow-list
        # stays meaningful in the fixture.
        base = {
            # A closed reference graph: run.sh cites the audit and the helper,
            # the helper cites run.sh again, and the README cites the helper.
            # No allow-listed file is named here.
            'tests-map.txt': 'audits/helper.py exists.\n',
            'audits/run.sh': 'python3 -B audits/check_repo_minimal.py\n'
                             'python3 -B audits/helper.py\n',
            'audits/helper.py': 'print(\"ok\")\n'
                                'Wraps run.sh.\n',

        }
        for rel, text in {**base, **files}.items():
            path = folder / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(textwrap.dedent(text))
        env = {'GIT_AUTHOR_NAME': 't', 'GIT_AUTHOR_EMAIL': 't@t',
               'GIT_COMMITTER_NAME': 't', 'GIT_COMMITTER_EMAIL': 't@t',
               'PATH': '/usr/local/bin:/usr/bin:/bin'}
        subprocess.run(['git', 'init', '-q'], cwd=folder, check=True)
        subprocess.run(['git', 'add', '-A'], cwd=folder, check=True)
        subprocess.run(['git', '-c', 'commit.gpgsign=false', 'commit', '-qm', 'x'],
                       cwd=folder, check=True, env=env)
        return folder

    def run_audit(self, folder):
        return subprocess.run(['python3', '-B', 'audits/check_repo_minimal.py'],
                              cwd=folder, text=True, capture_output=True,
                              timeout=20)

    def test_clean_repository_passes(self):
        result = self.run_audit(self.repo({}))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('repo-minimal: PASS', result.stdout)

    def test_unreferenced_script_is_rejected(self):
        result = self.run_audit(self.repo({'audits/orphan.py': 'print(1)\n'}))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('audits/orphan.py: not referenced', result.stderr)

    def test_tracked_tmp_log_and_plan_are_rejected(self):
        result = self.run_audit(self.repo({
            'tmp/gates/run.log': 'output\n',
            'plan.md': 'coordination plan\n',
        }))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('tmp/gates/run.log', result.stderr)
        self.assertIn('plan.md', result.stderr)

    def test_vendored_and_root_files_are_out_of_scope(self):
        result = self.run_audit(self.repo({
            'LeanFzn/Main.lean': 'def main : IO Unit := pure ()\n',
            'specification/minizinc-2.10.1/lib.html': '<html></html>\n',
        }))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_clean_fixture_has_no_orphans(self):
        result = self.run_audit(self.repo({'Tests/README.md':
                                           'The test-tree map.\n'}))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('1 allow-listed', result.stdout)


if __name__ == '__main__':
    unittest.main()
